import BstLean.Part268CellShard22Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12900_40 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (16539115680419 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113855571647 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨40, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (16539115680419 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113855571647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_41 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (10332704238303 / 12500000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (69616098591 / 3125000000000 : ℝ))
      (E := (cell12900 ⟨41, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (10332704238303 / 12500000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (69616098591 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_42 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41313856470503 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113859598659 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨42, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41313856470503 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113859598659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_43 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82593815476297 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445544642119 / 20000000000000 : ℝ))
      (E := (cell12900 ⟨43, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82593815476297 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445544642119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_44 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82559941482907 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (278465899171 / 12500000000000 : ℝ))
      (E := (cell12900 ⟨44, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82559941482907 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (278465899171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_45 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82526090931589 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227731202933 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨45, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82526090931589 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227731202933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_46 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41246131896623 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (556933809389 / 25000000000000 : ℝ))
      (E := (cell12900 ⟨46, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41246131896623 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (556933809389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_47 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (3298338401557 / 4000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227739236359 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨47, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (3298338401557 / 4000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227739236359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_48 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (4121233981991 / 5000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227743256063 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨48, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (4121233981991 / 5000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227743256063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_49 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82390922567269 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445549447063 / 20000000000000 : ℝ))
      (E := (cell12900 ⟨49, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82390922567269 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445549447063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_50 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82357188792751 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (111387561523 / 5000000000000 : ℝ))
      (E := (cell12900 ⟨50, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82357188792751 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (111387561523 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_51 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82323478287891 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227755238697 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨51, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82323478287891 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227755238697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_52 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41144895512227 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113879628509 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨52, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41144895512227 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113879628509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_53 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82256126974347 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113881641101 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨53, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82256126974347 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113881641101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_54 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82222486109617 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113883625863 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨54, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82222486109617 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113883625863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_55 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82188868402449 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (55694282003 / 2500000000000 : ℝ))
      (E := (cell12900 ⟨55, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82188868402449 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (55694282003 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_56 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82155273825169 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227775304467 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨56, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82155273825169 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227775304467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_57 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82121702350239 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445555864143 / 20000000000000 : ℝ))
      (E := (cell12900 ⟨57, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82121702350239 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445555864143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_58 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82088153950259 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227783324607 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨58, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82088153950259 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227783324607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_59 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (16410925719593 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113893655839 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨59, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (16410925719593 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113893655839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12901_40 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82695575901573 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556898617357 / 25000000000000 : ℝ))
      (E := (cell12901 ⟨40, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82695575901573 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556898617357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_41 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82661631701369 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227598426971 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨41, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82661631701369 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227598426971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_42 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82627711031009 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445520494951 / 20000000000000 : ℝ))
      (E := (cell12901 ⟨42, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82627711031009 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445520494951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_43 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41296906930477 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227606494089 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨43, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41296906930477 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227606494089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_44 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82559940161811 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113805241801 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨44, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82559940161811 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113805241801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_45 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (16505217980867 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556903625147 / 25000000000000 : ℝ))
      (E := (cell12901 ⟨45, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (16505217980867 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556903625147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_46 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82492263059431 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445523696881 / 20000000000000 : ℝ))
      (E := (cell12901 ⟨46, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82492263059431 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445523696881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_47 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (16491691919629 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445524498393 / 20000000000000 : ℝ))
      (E := (cell12901 ⟨47, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (16491691919629 / 20000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (445524498393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_48 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (10303084936459 / 12500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113813260553 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨48, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (10303084936459 / 12500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113813260553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_49 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82390922711351 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (278453813809 / 12500000000000 : ℝ))
      (E := (cell12901 ⟨49, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82390922711351 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (278453813809 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_50 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82357189228663 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (278454314551 / 12500000000000 : ℝ))
      (E := (cell12901 ⟨50, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82357189228663 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (278454314551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_51 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82323479015231 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113819268057 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨51, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82323479015231 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113819268057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_52 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82289792042823 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227642566579 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨52, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82289792042823 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227642566579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_53 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41128064141673 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (278455818189 / 12500000000000 : ℝ))
      (E := (cell12901 ⟨53, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41128064141673 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (278455818189 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_54 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82222487708847 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227650587603 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨54, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82222487708847 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227650587603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_55 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82188870291513 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227654571047 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨55, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82188870291513 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227654571047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_56 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82155276003669 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (69614329721 / 3125000000000 : ℝ))
      (E := (cell12901 ⟨56, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82155276003669 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (69614329721 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_57 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82121704817779 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227662582789 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨57, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82121704817779 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227662582789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_58 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82088156706443 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227666602821 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨58, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82088156706443 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227666602821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_59 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82054631642397 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113835303353 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨59, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82054631642397 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113835303353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12902_40 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41347786700937 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227477733793 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨40, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41347786700937 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227477733793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_41 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (826616294971 / 1000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (278435219357 / 12500000000000 : ℝ))
      (E := (cell12902 ⟨41, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (826616294971 / 1000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (278435219357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_42 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (16525541824353 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227485749261 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨42, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (16525541824353 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227485749261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_43 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82593812246327 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227489774691 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨43, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82593812246327 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227489774691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_44 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (20639984710349 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (111374688549 / 5000000000000 : ℝ))
      (E := (cell12902 ⟨44, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (20639984710349 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (111374688549 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_45 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (2578940277429 / 3125000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113748897711 / 50000000000000 : ℝ))
      (E := (cell12902 ⟨45, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (2578940277429 / 3125000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113748897711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_46 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82492262326227 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (139218861711 / 6250000000000 : ℝ))
      (E := (cell12902 ⟨46, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82492262326227 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (139218861711 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_47 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82458459157941 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227505803753 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨47, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82458459157941 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227505803753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_48 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41212339672033 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556877460597 / 25000000000000 : ℝ))
      (E := (cell12902 ⟨48, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41212339672033 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556877460597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_49 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82390922855941 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227513841927 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨49, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82390922855941 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227513841927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_50 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41178594832523 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445503571743 / 20000000000000 : ℝ))
      (E := (cell12902 ⟨50, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41178594832523 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445503571743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_51 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82323479743009 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227521830923 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨51, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82323479743009 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227521830923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_52 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (16457958612319 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227525873569 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨52, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (16457958612319 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227525873569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_53 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82256129592713 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227529865357 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨53, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82256129592713 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227529865357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_54 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82222489308411 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227533861883 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨54, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82222489308411 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227533861883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_55 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (20547218045219 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556884464877 / 25000000000000 : ℝ))
      (E := (cell12902 ⟨55, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (20547218045219 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (556884464877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_56 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41077639091217 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227541913529 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨56, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41077639091217 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227541913529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_57 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82121707285549 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (34805404713 / 1562500000000 : ℝ))
      (E := (cell12902 ⟨57, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82121707285549 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (34805404713 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_58 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82088159462823 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (89101995147 / 4000000000000 : ℝ))
      (E := (cell12902 ⟨58, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82088159462823 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (89101995147 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_59 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (5128414667937 / 6250000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (139222118713 / 6250000000000 : ℝ))
      (E := (cell12902 ⟨59, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (5128414667937 / 6250000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (139222118713 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12903_40 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82695570902997 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556840278173 / 25000000000000 : ℝ))
      (E := (cell12903 ⟨40, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82695570902997 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556840278173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_41 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82661627293619 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227365079777 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨41, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82661627293619 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227365079777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_42 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (10328463401659 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (445473815931 / 20000000000000 : ℝ))
      (E := (cell12903 ⟨42, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (10328463401659 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (445473815931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_43 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82593810632417 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113686555619 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨43, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82593810632417 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113686555619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_44 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82559937521663 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113688557181 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨44, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82559937521663 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113688557181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_45 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82526087851767 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227381146321 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨45, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82526087851767 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227381146321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_46 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41246130796817 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278423143309 / 12500000000000 : ℝ))
      (E := (cell12903 ⟨46, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41246130796817 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278423143309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_47 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41229229359157 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227389112793 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨47, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41229229359157 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227389112793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_48 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41212339598501 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113696580479 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨48, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41212339598501 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113696580479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_49 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82390923001037 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227397170707 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨49, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82390923001037 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227397170707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_50 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41178595050951 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (111370056969 / 5000000000000 : ℝ))
      (E := (cell12903 ⟨50, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41178595050951 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (111370056969 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_51 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (10290435058903 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278425647769 / 12500000000000 : ℝ))
      (E := (cell12903 ⟨51, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (10290435058903 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278425647769 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_52 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (8228979408077 / 10000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556852294497 / 25000000000000 : ℝ))
      (E := (cell12903 ⟨52, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (8228979408077 / 10000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556852294497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_53 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (5141008181403 / 6250000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556853295667 / 25000000000000 : ℝ))
      (E := (cell12903 ⟨53, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (5141008181403 / 6250000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556853295667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_54 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (20555622727077 / 25000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (55685429819 / 2500000000000 : ℝ))
      (E := (cell12903 ⟨54, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (20555622727077 / 25000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (55685429819 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_55 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82188874070537 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (17819369637 / 800000000000 : ℝ))
      (E := (cell12903 ⟨55, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82188874070537 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (17819369637 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_56 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41077640180731 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113712607209 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨56, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41077640180731 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113712607209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_57 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82121709753549 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227429218083 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨57, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82121709753549 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227429218083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_58 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41044081109699 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227433211361 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨58, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41044081109699 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227433211361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_59 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82054637731747 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227437249 / 100000000000 : ℝ))
      (E := (cell12903 ⟨59, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82054637731747 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227437249 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12904_40 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82695568404941 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113622214913 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨40, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82695568404941 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113622214913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_41 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20665406272731 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (89089938421 / 4000000000000 : ℝ))
      (E := (cell12904 ⟨41, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20665406272731 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (89089938421 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_42 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (8262770530553 / 10000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113626232967 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨42, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (8262770530553 / 10000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113626232967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_43 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82593809019223 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227256444893 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨43, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82593809019223 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227256444893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_44 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82559936202611 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227260454889 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨44, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82559936202611 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227260454889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_45 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82526086826453 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227264494399 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨45, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82526086826453 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227264494399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_46 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82492260861653 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113634251391 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨46, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82492260861653 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113634251391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_47 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82458458279263 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445454495603 / 20000000000000 : ℝ))
      (E := (cell12904 ⟨47, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82458458279263 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445454495603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_48 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (41212339525239 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227276476817 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨48, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (41212339525239 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227276476817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_49 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82390923146639 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (222728049681 / 10000000000000 : ℝ))
      (E := (cell12904 ⟨49, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82390923146639 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (222728049681 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_50 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (8235719053923 / 10000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445456907081 / 20000000000000 : ℝ))
      (E := (cell12904 ⟨50, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (8235719053923 / 10000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445456907081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_51 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20580870299969 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (89091541231 / 4000000000000 : ℝ))
      (E := (cell12904 ⟨51, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20580870299969 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (89091541231 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_52 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82289795100347 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113646269443 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨52, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82289795100347 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113646269443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_53 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82256132212551 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445459311303 / 20000000000000 : ℝ))
      (E := (cell12904 ⟨53, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82256132212551 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445459311303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_54 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (41111246254269 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (278412572529 / 12500000000000 : ℝ))
      (E := (cell12904 ⟨54, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (41111246254269 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (278412572529 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_55 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82188875960497 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113652273639 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨55, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82188875960497 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113652273639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_56 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (16431056508151 / 20000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227308572019 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨56, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (16431056508151 / 20000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227308572019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_57 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82121712221779 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445462518261 / 20000000000000 : ℝ))
      (E := (cell12904 ⟨57, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82121712221779 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445462518261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_58 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82088164976169 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227316600877 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨58, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82088164976169 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227316600877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_59 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (10256830097083 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227320596269 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨59, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (10256830097083 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227320596269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12905_40 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82695565907707 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278390975341 / 12500000000000 : ℝ))
      (E := (cell12905 ⟨40, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82695565907707 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278390975341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_41 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (16532324577803 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278391479789 / 12500000000000 : ℝ))
      (E := (cell12905 ⟨41, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (16532324577803 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278391479789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_42 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (4131385169927 / 5000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278391981161 / 12500000000000 : ℝ))
      (E := (cell12905 ⟨42, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (4131385169927 / 5000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278391981161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_43 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (10324225925843 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227139834497 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨43, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (10324225925843 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227139834497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_44 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82559934884239 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (69598245357 / 3125000000000 : ℝ))
      (E := (cell12905 ⟨44, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82559934884239 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (69598245357 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_45 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (10315760725223 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227147839661 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨45, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (10315760725223 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227147839661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_46 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82492260130283 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227151856311 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨46, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82492260130283 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227151856311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_47 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (20614614460197 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113577949711 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨47, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (20614614460197 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113577949711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_48 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (5151542431531 / 6250000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227159907873 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨48, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (5151542431531 / 6250000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227159907873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_49 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (20597730823187 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (139197742451 / 6250000000000 : ℝ))
      (E := (cell12905 ⟨49, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (20597730823187 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (139197742451 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_50 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82357190977029 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278395991099 / 12500000000000 : ℝ))
      (E := (cell12905 ⟨50, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82357190977029 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278395991099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_51 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (16464696385793 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227171935819 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨51, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (16464696385793 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227171935819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_52 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41144898060163 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445435179443 / 20000000000000 : ℝ))
      (E := (cell12905 ⟨52, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41144898060163 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445435179443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_53 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82256133523021 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (222717992783 / 10000000000000 : ℝ))
      (E := (cell12905 ⟨53, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82256133523021 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (222717992783 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_54 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82222494109101 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227183965207 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨54, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82222494109101 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227183965207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_55 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (20547219462689 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113593973293 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨55, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (20547219462689 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113593973293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_56 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82155284720313 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113595993167 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨56, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82155284720313 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113595993167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_57 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41060857345119 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278399495267 / 12500000000000 : ℝ))
      (E := (cell12905 ⟨57, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41060857345119 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278399495267 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_58 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (16417633546627 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556799997009 / 25000000000000 : ℝ))
      (E := (cell12905 ⟨58, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (16417633546627 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556799997009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_59 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41027321910871 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556801000107 / 25000000000000 : ℝ))
      (E := (cell12905 ⟨59, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41027321910871 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556801000107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12906_40 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (16539112682259 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (11135056157 / 500000000000 : ℝ))
      (E := (cell12906 ⟨40, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (16539112682259 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (11135056157 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_41 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (20665405171973 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227015271929 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨41, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (20665405171973 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227015271929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_42 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (826277014923 / 1000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113509614859 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨42, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (826277014923 / 1000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113509614859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_43 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41296902897491 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227023280049 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨43, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41296902897491 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227023280049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_44 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82559933566549 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (139189202819 / 6250000000000 : ℝ))
      (E := (cell12906 ⟨44, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82559933566549 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (139189202819 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_45 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82526084777761 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227031299873 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨45, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82526084777761 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227031299873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_46 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82492259399523 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227035265967 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨46, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82492259399523 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227035265967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_47 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82458457402889 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227039318083 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨47, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82458457402889 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227039318083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_48 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (16484935751811 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445408655453 / 20000000000000 : ℝ))
      (E := (cell12906 ⟨48, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (16484935751811 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445408655453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_49 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82390923439363 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (89081892717 / 4000000000000 : ℝ))
      (E := (cell12906 ⟨49, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82390923439363 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (89081892717 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_50 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82357191415299 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (111352565977 / 5000000000000 : ℝ))
      (E := (cell12906 ⟨50, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82357191415299 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (111352565977 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_51 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82323482658491 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (111352766913 / 5000000000000 : ℝ))
      (E := (cell12906 ⟨51, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82323482658491 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (111352766913 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_52 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82289797140707 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (89082372481 / 4000000000000 : ℝ))
      (E := (cell12906 ⟨52, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82289797140707 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (89082372481 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_53 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82256134833859 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (556765838921 / 25000000000000 : ℝ))
      (E := (cell12906 ⟨53, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82256134833859 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (556765838921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_54 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82222495709997 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445413469537 / 20000000000000 : ℝ))
      (E := (cell12906 ⟨54, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82222495709997 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445413469537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_55 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82188879741313 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227071343433 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨55, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82188879741313 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227071343433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_56 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41077643450067 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (139192212389 / 6250000000000 : ℝ))
      (E := (cell12906 ⟨56, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41077643450067 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (139192212389 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_57 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82121717158927 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227079389741 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨57, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82121717158927 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227079389741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_58 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (10261021311287 / 12500000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (55677084321 / 2500000000000 : ℝ))
      (E := (cell12906 ⟨58, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (10261021311287 / 12500000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (55677084321 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_59 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82054646866981 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227087402267 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨59, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82054646866981 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227087402267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12907_40 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82695560915703 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556723664269 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨40, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82695560915703 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556723664269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_41 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (16532323697511 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445379740517 / 20000000000000 : ℝ))
      (E := (cell12907 ⟨41, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (16532323697511 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445379740517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_42 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82627699586811 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226902666037 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨42, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82627699586811 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226902666037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_43 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (16518760836787 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (278363340339 / 12500000000000 : ℝ))
      (E := (cell12907 ⟨43, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (16518760836787 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (278363340339 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_44 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82559932249539 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226910694793 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨44, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82559932249539 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226910694793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_45 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82526083754383 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445382939677 / 20000000000000 : ℝ))
      (E := (cell12907 ⟨45, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82526083754383 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445382939677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_46 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41246129334687 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556729682937 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨46, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41246129334687 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556729682937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_47 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (16491691393113 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113461367 / 50000000000 : ℝ))
      (E := (cell12907 ⟨47, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (16491691393113 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113461367 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_48 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (16484935722831 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (17397865327 / 781250000000 : ℝ))
      (E := (cell12907 ⟨48, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (16484935722831 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (17397865327 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_49 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (16478184717297 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (55673268849 / 2500000000000 : ℝ))
      (E := (cell12907 ⟨49, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (16478184717297 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (55673268849 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_50 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82357191854041 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (44538695333 / 2000000000000 : ℝ))
      (E := (cell12907 ⟨50, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82357191854041 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (44538695333 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_51 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82323483388453 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113469369049 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨51, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82323483388453 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113469369049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_52 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (8228979816149 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556735695829 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨52, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (8228979816149 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556735695829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_53 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (10282017018133 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113473390503 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨53, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (10282017018133 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113473390503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_54 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41111248655613 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226950786761 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨54, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41111248655613 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226950786761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_55 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (10273610204021 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113477398469 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨55, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (10273610204021 / 12500000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113477398469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_56 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82155289080219 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226958807687 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨56, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82155289080219 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226958807687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_57 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (16424343925569 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445392562991 / 20000000000000 : ℝ))
      (E := (cell12907 ⟨57, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (16424343925569 / 20000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445392562991 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_58 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (20522043311913 / 25000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226966814477 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨58, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (20522043311913 / 25000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226966814477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_59 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (4102732495619 / 5000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113485430499 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨59, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (4102732495619 / 5000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113485430499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12908_40 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (20673889605233 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226778138523 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨40, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (20673889605233 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226778138523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_41 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82661616288003 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226782130281 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨41, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82661616288003 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226782130281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_42 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82627697682073 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556696539561 / 25000000000000 : ℝ))
      (E := (cell12908 ⟨42, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82627697682073 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556696539561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_43 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82593802573603 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226790162487 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨43, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82593802573603 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226790162487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_44 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82559930933209 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (222679414163 / 10000000000000 : ℝ))
      (E := (cell12908 ⟨44, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82559930933209 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (222679414163 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_45 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (1650521654633 / 2000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556699538241 / 25000000000000 : ℝ))
      (E := (cell12908 ⟨45, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (1650521654633 / 2000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556699538241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_46 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (16498451587967 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (8907208779 / 400000000000 : ℝ))
      (E := (cell12908 ⟨46, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (16498451587967 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (8907208779 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_47 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82458456528817 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113403103051 / 50000000000000 : ℝ))
      (E := (cell12908 ⟨47, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82458456528817 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113403103051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_48 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (16484935693959 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226810184783 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨48, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (16484935693959 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226810184783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_49 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (2574716366691 / 3125000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226814187321 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨49, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (2574716366691 / 3125000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226814187321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_50 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41178596146627 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226818211123 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨50, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41178596146627 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226818211123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_51 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (20580871029713 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113411126691 / 50000000000000 : ℝ))
      (E := (cell12908 ⟨51, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (20580871029713 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113411126691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_52 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (3291591967307 / 4000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226826252039 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨52, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (3291591967307 / 4000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226826252039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_53 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (20564034364159 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556707565717 / 25000000000000 : ℝ))
      (E := (cell12908 ⟨53, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (20564034364159 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556707565717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_54 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (20555624728197 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (111341711167 / 5000000000000 : ℝ))
      (E := (cell12908 ⟨54, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (20555624728197 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (111341711167 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_55 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41094441761661 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (111341912399 / 5000000000000 : ℝ))
      (E := (cell12908 ⟨55, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41094441761661 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (111341912399 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_56 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82155291260567 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556710568467 / 25000000000000 : ℝ))
      (E := (cell12908 ⟨56, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82155291260567 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556710568467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_57 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82121722096993 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (139177893559 / 6250000000000 : ℝ))
      (E := (cell12908 ⟨57, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82121722096993 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (139177893559 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_58 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (20522044001301 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113425156473 / 50000000000000 : ℝ))
      (E := (cell12908 ⟨58, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (20522044001301 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113425156473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_59 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82054652957941 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226854317407 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨59, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82054652957941 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226854317407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12909_40 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82695555926981 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (139166351061 / 6250000000000 : ℝ))
      (E := (cell12909 ⟨40, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82695555926981 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (139166351061 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_41 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82661614089237 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226665613809 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨41, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82661614089237 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226665613809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_42 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (20656923944521 / 25000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226669647531 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨42, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (20656923944521 / 25000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226669647531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_43 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82593800963987 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226673658213 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨43, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82593800963987 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226673658213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_44 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82559929617559 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226677644477 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨44, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82559929617559 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226677644477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_45 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82526081709563 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226681663613 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨45, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82526081709563 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226681663613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_46 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82492257210907 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226685654971 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨46, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82492257210907 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226685654971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_47 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (20614614023161 / 25000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226689675461 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨47, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (20614614023161 / 25000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226689675461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_48 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (3296987133039 / 4000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226693663959 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨48, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (3296987133039 / 4000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226693663959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_49 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (20597730970561 / 25000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226697676989 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨49, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (20597730970561 / 25000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226697676989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_50 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41178596366469 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (55667542799 / 2500000000000 : ℝ))
      (E := (cell12909 ⟨50, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41178596366469 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (55667542799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_51 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41161742424843 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226705707043 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨51, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41161742424843 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226705707043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_52 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82289800204261 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113354859099 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨52, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82289800204261 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113354859099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_53 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (1285252168259 / 1562500000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (11133568711 / 500000000000 : ℝ))
      (E := (cell12909 ⟨53, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (1285252168259 / 1562500000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (11133568711 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_54 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41111250257341 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226717716521 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨54, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41111250257341 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226717716521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_55 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82188885414773 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226721755683 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨55, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82188885414773 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226721755683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_56 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82155293441179 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226725737623 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨56, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82155293441179 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226725737623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_57 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (8212172456637 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (69585305517 / 3125000000000 : ℝ))
      (E := (cell12909 ⟨57, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (8212172456637 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (69585305517 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_58 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (1641763575259 / 2000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226733749873 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨58, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (1641763575259 / 2000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226733749873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_59 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41027328001831 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113368885749 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨59, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41027328001831 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113368885749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12910_40 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82695553433851 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226545151201 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨40, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82695553433851 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226545151201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_41 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (10332701486407 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (222654915317 / 10000000000000 : ℝ))
      (E := (cell12910 ⟨41, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (10332701486407 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (222654915317 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_42 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41313846937423 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113276566947 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨42, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41313846937423 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113276566947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_43 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (16518759871017 / 20000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226557151053 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨43, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (16518759871017 / 20000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226557151053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_44 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82559928302589 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113280572237 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨44, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82559928302589 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113280572237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_45 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82526080688121 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113282585723 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨45, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82526080688121 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113282585723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_46 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20623064120647 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113284585661 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨46, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20623064120647 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113284585661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_47 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41229227828523 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226573201009 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨47, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41229227828523 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226573201009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_48 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (10303084772837 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (111328859969 / 5000000000000 : ℝ))
      (E := (cell12910 ⟨48, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (10303084772837 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (111328859969 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_49 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41195462015441 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226581222963 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨49, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41195462015441 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226581222963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_50 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20589298293273 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113292605081 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨50, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20589298293273 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113292605081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_51 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82323485580957 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113294608563 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨51, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82323485580957 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113294608563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_52 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82289801226249 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113296620419 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨52, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82289801226249 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113296620419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_53 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41128070040441 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113298609501 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨53, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41128070040441 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113298609501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_54 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20555625529227 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113300633151 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨54, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20555625529227 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113300633151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_55 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41094443653261 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226605260927 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨55, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41094443653261 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226605260927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_56 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (16431059124411 / 20000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (139163078631 / 6250000000000 : ℝ))
      (E := (cell12910 ⟨56, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (16431059124411 / 20000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (139163078631 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_57 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (10265215879497 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113306626877 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨57, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (10265215879497 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113306626877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_58 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82088181520891 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (89064692113 / 4000000000000 : ℝ))
      (E := (cell12910 ⟨58, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82088181520891 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (89064692113 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_59 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82054659049543 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226621282483 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨59, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82054659049543 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226621282483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12911_40 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82695550941541 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113214341217 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨40, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82695550941541 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113214341217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_41 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (4133080484703 / 5000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113216344787 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨41, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (4133080484703 / 5000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113216344787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_42 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82627691972357 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278304584519 / 12500000000000 : ℝ))
      (E := (cell12911 ⟨42, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82627691972357 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278304584519 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_43 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41296898873449 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113220349923 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨43, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41296898873449 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113220349923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_44 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82559926988299 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226444700483 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨44, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82559926988299 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226444700483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_45 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82526079667323 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278306091919 / 12500000000000 : ℝ))
      (E := (cell12911 ⟨45, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82526079667323 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278306091919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_46 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82492255754879 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556613185951 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨46, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82492255754879 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556613185951 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_47 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82458455222023 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113228361907 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨47, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82458455222023 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113228361907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_48 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82424678039957 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (34788448939 / 1562500000000 : ℝ))
      (E := (cell12911 ⟨48, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82424678039957 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (34788448939 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_49 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41195462090013 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113232383133 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨49, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41195462090013 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113232383133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_50 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82357193613717 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (222646876473 / 10000000000000 : ℝ))
      (E := (cell12911 ⟨50, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82357193613717 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (222646876473 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_51 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (10290435789083 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445294556727 / 20000000000000 : ℝ))
      (E := (cell12911 ⟨51, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (10290435789083 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445294556727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_52 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41144901124319 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556619190229 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨52, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41144901124319 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556619190229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_53 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (16451228278711 / 20000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226480811419 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨53, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (16451228278711 / 20000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226480811419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_54 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82222503719467 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (222648481359 / 10000000000000 : ℝ))
      (E := (cell12911 ⟨54, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82222503719467 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (222648481359 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_55 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (8218888919857 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (222648882283 / 10000000000000 : ℝ))
      (E := (cell12911 ⟨55, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (8218888919857 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (222648882283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_56 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41077648901597 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (222649283529 / 10000000000000 : ℝ))
      (E := (cell12911 ⟨56, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41077648901597 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (222649283529 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_57 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82121729505811 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226496846909 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨57, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82121729505811 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226496846909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_58 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82088184279027 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (139156303339 / 6250000000000 : ℝ))
      (E := (cell12911 ⟨58, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82088184279027 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (139156303339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_59 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (16410932419117 / 20000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226504850363 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨59, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (16410932419117 / 20000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226504850363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12912_40 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82695548450051 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113156134721 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨40, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82695548450051 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113156134721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_41 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82661607497649 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (111315811151 / 5000000000000 : ℝ))
      (E := (cell12912 ⟨41, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82661607497649 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (111315811151 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_42 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41313845035309 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226320274303 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨42, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41313845035309 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226320274303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_43 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41296898069713 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226324245753 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨43, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41296898069713 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226324245753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_44 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (1289998838667 / 1562500000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226328253643 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨44, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (1289998838667 / 1562500000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226328253643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_45 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82526078647169 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445266459289 / 20000000000000 : ℝ))
      (E := (cell12912 ⟨45, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82526078647169 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445266459289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_46 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (4124612751389 / 5000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556584078377 / 25000000000000 : ℝ))
      (E := (cell12912 ⟨46, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (4124612751389 / 5000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556584078377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_47 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (3298338191503 / 4000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226340302809 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨47, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (3298338191503 / 4000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226340302809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_48 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41212338948879 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (111317216053 / 5000000000000 : ℝ))
      (E := (cell12912 ⟨48, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41212338948879 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (111317216053 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_49 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41195462164837 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226348306899 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨49, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41195462164837 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226348306899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_50 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82357194054813 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226352316663 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨50, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82357194054813 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226352316663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_51 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41161743522403 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445271269509 / 20000000000000 : ℝ))
      (E := (cell12912 ⟨51, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41161743522403 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445271269509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_52 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82289803271429 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226360337477 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨52, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82289803271429 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226360337477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_53 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41128071353297 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556591085559 / 25000000000000 : ℝ))
      (E := (cell12912 ⟨53, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41128071353297 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556591085559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_54 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41111252661179 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (139148022399 / 6250000000000 : ℝ))
      (E := (cell12912 ⟨54, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41111252661179 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (139148022399 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_55 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41094445545457 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556593095569 / 25000000000000 : ℝ))
      (E := (cell12912 ⟨55, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41094445545457 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556593095569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_56 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (20538824996149 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113188175459 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨56, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (20538824996149 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113188175459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_57 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (656973855807 / 800000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (222638037851 / 10000000000000 : ℝ))
      (E := (cell12912 ⟨57, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (656973855807 / 800000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (222638037851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_58 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82088187037357 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (222638440167 / 10000000000000 : ℝ))
      (E := (cell12912 ⟨58, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82088187037357 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (222638440167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_59 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82054665141787 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (89055536637 / 4000000000000 : ℝ))
      (E := (cell12912 ⟨59, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82054665141787 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (89055536637 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12913_40 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (4134777297969 / 5000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226195853459 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨40, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (4134777297969 / 5000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226195853459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_41 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82661605302021 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445239974219 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨41, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82661605302021 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445239974219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_42 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (20656922042407 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445240773907 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨42, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (20656922042407 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445240773907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_43 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82593794532667 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (34784497619 / 1562500000000 : ℝ))
      (E := (cell12913 ⟨43, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82593794532667 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (34784497619 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_44 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82559924361757 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (69569120713 / 3125000000000 : ℝ))
      (E := (cell12913 ⟨44, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82559924361757 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (69569120713 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_45 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (4126303881383 / 5000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (89048634189 / 4000000000000 : ℝ))
      (E := (cell12913 ⟨45, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (4126303881383 / 5000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (89048634189 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_46 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82492254301289 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113109940219 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨46, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82492254301289 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113109940219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_47 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82458454353701 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445244775813 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨47, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82458454353701 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445244775813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_48 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41212338878049 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (55655697683 / 2500000000000 : ℝ))
      (E := (cell12913 ⟨48, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41212338878049 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (55655697683 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_49 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (20597731119957 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226231903841 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨49, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (20597731119957 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226231903841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_50 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82357194496379 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556558981241 / 25000000000000 : ℝ))
      (E := (cell12913 ⟨50, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82357194496379 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556558981241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_51 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (16464697555477 / 20000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (278279988607 / 12500000000000 : ℝ))
      (E := (cell12913 ⟨51, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (16464697555477 / 20000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (278279988607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_52 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (4114490214731 / 5000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556560977869 / 25000000000000 : ℝ))
      (E := (cell12913 ⟨52, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (4114490214731 / 5000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556560977869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_53 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (4112807201 / 5000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226247929597 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨53, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (4112807201 / 5000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226247929597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_54 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (4111125346279 / 5000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226251959783 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨54, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (4111125346279 / 5000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226251959783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_55 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (20547223245889 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113127969633 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨55, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (20547223245889 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113127969633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_56 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41077651083131 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226259982409 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨56, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41077651083131 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226259982409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_57 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82121734446167 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556565991723 / 25000000000000 : ℝ))
      (E := (cell12913 ⟨57, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82121734446167 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556565991723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_58 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82088189795881 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556567001689 / 25000000000000 : ℝ))
      (E := (cell12913 ⟨58, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82088189795881 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556567001689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_59 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82054668188149 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556567994793 / 25000000000000 : ℝ))
      (E := (cell12913 ⟨59, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82054668188149 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556567994793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12914_40 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (10336942933691 / 12500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (445215886897 / 20000000000000 : ℝ))
      (E := (cell12914 ⟨40, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (10336942933691 / 12500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (445215886897 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_41 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41330801553589 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (139130216089 / 6250000000000 : ℝ))
      (E := (cell12914 ⟨41, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41330801553589 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (139130216089 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_42 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (82627686269387 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (278260932731 / 12500000000000 : ℝ))
      (E := (cell12914 ⟨42, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (82627686269387 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (278260932731 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_43 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (82593792926623 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226091505433 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨43, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (82593792926623 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226091505433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_44 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (2579997595297 / 3125000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226095469143 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨44, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (2579997595297 / 3125000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226095469143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_45 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (16505215321759 / 20000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226099469079 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨45, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (16505215321759 / 20000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226099469079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_46 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (82492253575409 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113051751749 / 50000000000000 : ℝ))
      (E := (cell12914 ⟨46, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (82492253575409 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113051751749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_47 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41229226960201 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226107511511 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨47, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41229226960201 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226107511511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_48 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41212338807489 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556527872719 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨48, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41212338807489 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556527872719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_49 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41195462315243 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (445223099623 / 20000000000000 : ℝ))
      (E := (cell12914 ⟨49, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41195462315243 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (445223099623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_50 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41178597469207 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226119530633 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨50, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41178597469207 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226119530633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_51 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41161744255199 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (445224705319 / 20000000000000 : ℝ))
      (E := (cell12914 ⟨51, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41161744255199 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (445224705319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_52 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (20572451329553 / 25000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113063770981 / 50000000000000 : ℝ))
      (E := (cell12914 ⟨52, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (20572451329553 / 25000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113063770981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_53 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (20564036333443 / 25000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (8695826459 / 390625000000 : ℝ))
      (E := (cell12914 ⟨53, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (20564036333443 / 25000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (8695826459 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_54 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (16444501705827 / 20000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (69566736209 / 3125000000000 : ℝ))
      (E := (cell12914 ⟨54, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (16444501705827 / 20000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (69566736209 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_55 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (5136805929781 / 6250000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226139552917 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨55, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (5136805929781 / 6250000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226139552917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_56 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (8215530434819 / 10000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (55653590287 / 2500000000000 : ℝ))
      (E := (cell12914 ⟨56, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (8215530434819 / 10000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (55653590287 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_57 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (5132608557293 / 6250000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226147612053 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨57, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (5132608557293 / 6250000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226147612053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_58 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (410440962773 / 500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226151609489 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨58, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (410440962773 / 500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226151609489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_59 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (82054671234671 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556538899829 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨59, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (82054671234671 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556538899829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12915_40 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (5168471311281 / 6250000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (278245383911 / 12500000000000 : ℝ))
      (E := (cell12915 ⟨40, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (5168471311281 / 6250000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (278245383911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_41 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82661600913119 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225967099589 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨41, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82661600913119 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225967099589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_42 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (16525536873979 / 20000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112985555029 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨42, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (16525536873979 / 20000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112985555029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_43 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82593791321293 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222597510153 / 10000000000000 : ℝ))
      (E := (cell12915 ⟨43, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82593791321293 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222597510153 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_44 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (8255992173793 / 10000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445195826297 / 20000000000000 : ℝ))
      (E := (cell12915 ⟨44, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (8255992173793 / 10000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445195826297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_45 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41263037795287 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225983139507 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨45, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41263037795287 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225983139507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_46 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82492252850137 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (278248390473 / 12500000000000 : ℝ))
      (E := (cell12915 ⟨46, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82492252850137 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (278248390473 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_47 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (20614613371919 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225991141219 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨47, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (20614613371919 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225991141219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_48 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41212338737199 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225995189637 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨48, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41212338737199 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225995189637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_49 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (5149432798853 / 6250000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225999148699 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨49, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (5149432798853 / 6250000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225999148699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_50 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (2058929884523 / 2500000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222600319267 / 10000000000000 : ℝ))
      (E := (cell12915 ⟨50, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (2058929884523 / 2500000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222600319267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_51 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82323489243847 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1113003600381 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨51, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82323489243847 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1113003600381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_52 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (20572451585551 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1113005584943 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨52, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (20572451585551 / 25000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1113005584943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_53 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (8225614664791 / 10000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445203042977 / 20000000000000 : ℝ))
      (E := (cell12915 ⟨53, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (8225614664791 / 10000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445203042977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_54 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82222510133021 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (11130096071 / 500000000000 : ℝ))
      (E := (cell12915 ⟨54, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82222510133021 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (11130096071 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_55 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82188896769733 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (34781612863 / 1562500000000 : ℝ))
      (E := (cell12915 ⟨55, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82188896769733 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (34781612863 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_56 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82155306530381 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2226027238129 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨56, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82155306530381 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2226027238129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_57 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41060869693719 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (556507813707 / 25000000000000 : ℝ))
      (E := (cell12915 ⟨57, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41060869693719 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (556507813707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_58 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82088195313513 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1113017634531 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨58, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82088195313513 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1113017634531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_59 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82054674281353 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1113019638179 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨59, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82054674281353 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1113019638179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12916_40 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41347769246141 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225846763871 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨40, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41347769246141 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225846763871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_41 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (20665399679961 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (278231349699 / 12500000000000 : ℝ))
      (E := (cell12916 ⟨41, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (20665399679961 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (278231349699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_42 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (5164230154447 / 6250000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (44517095107 / 2000000000000 : ℝ))
      (E := (cell12916 ⟨42, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (5164230154447 / 6250000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (44517095107 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_43 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (20648447429169 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112929406211 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨43, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (20648447429169 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112929406211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_44 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (16511984085407 / 20000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225862790981 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨44, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (16511984085407 / 20000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225862790981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_45 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (20631518643249 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225866807127 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨45, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (20631518643249 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225866807127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_46 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (82492252125473 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445174160041 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨46, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (82492252125473 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445174160041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_47 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (3298338122221 / 4000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (27823435339 / 1250000000000 : ℝ))
      (E := (cell12916 ⟨47, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (3298338122221 / 4000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (27823435339 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_48 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (20606169333589 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112939413371 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨48, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (20606169333589 / 25000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112939413371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_49 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (16478184986663 / 20000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445176571119 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨49, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (16478184986663 / 20000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445176571119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_50 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (16471439164779 / 20000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225886852077 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨50, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (16471439164779 / 20000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225886852077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_51 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (8232348997773 / 10000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445178174467 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨51, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (8232348997773 / 10000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445178174467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_52 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41144903683299 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112947427149 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨52, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41144903683299 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112947427149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_53 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41128073981207 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225898853741 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨53, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41128073981207 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225898853741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_54 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41111255868619 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225902867221 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨54, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41111255868619 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225902867221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_55 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41094449331633 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112953445547 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨55, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41094449331633 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112953445547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_56 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41077654356417 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225910921503 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨56, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41077654356417 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225910921503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_57 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (5132608866151 / 6250000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225914895219 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨57, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (5132608866151 / 6250000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225914895219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_58 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (82088198072621 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445183785257 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨58, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (82088198072621 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445183785257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_59 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (16410935465639 / 20000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445184590217 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨59, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (16410935465639 / 20000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445184590217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12917_40 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82695536004887 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278216306683 / 12500000000000 : ℝ))
      (E := (cell12917 ⟨40, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82695536004887 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278216306683 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_41 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (10332699565919 / 12500000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112867246321 / 50000000000000 : ℝ))
      (E := (cell12917 ⟨41, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (10332699565919 / 12500000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112867246321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_42 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82627680573157 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (111286922827 / 5000000000000 : ℝ))
      (E := (cell12917 ⟨42, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82627680573157 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (111286922827 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_43 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (20648447028193 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445148492319 / 20000000000000 : ℝ))
      (E := (cell12917 ⟨43, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (20648447028193 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445148492319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_44 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41279959558409 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225746506493 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨44, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41279959558409 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225746506493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_45 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41263036778031 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445150094387 / 20000000000000 : ℝ))
      (E := (cell12917 ⟨45, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41263036778031 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445150094387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_46 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82492251401419 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (55643863319 / 2500000000000 : ℝ))
      (E := (cell12917 ⟨46, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82492251401419 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (55643863319 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_47 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82458452623947 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225758510283 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨47, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82458452623947 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225758510283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_48 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82424677194853 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (22257625201 / 1000000000000 : ℝ))
      (E := (cell12917 ⟨48, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82424677194853 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (22257625201 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_49 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82390925085487 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225766559823 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨49, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82390925085487 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225766559823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_50 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (4117859813367 / 5000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112885283927 / 50000000000000 : ℝ))
      (E := (cell12917 ⟨50, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (4117859813367 / 5000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112885283927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_51 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82323490712049 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (222577454131 / 10000000000000 : ℝ))
      (E := (cell12917 ⟨51, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82323490712049 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (222577454131 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_52 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82289808391391 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (44515570723 / 2000000000000 : ℝ))
      (E := (cell12917 ⟨52, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82289808391391 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (44515570723 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_53 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (20564037319321 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225782549143 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨53, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (20564037319321 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225782549143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_54 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82222513341787 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139111661053 / 6250000000000 : ℝ))
      (E := (cell12917 ⟨54, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82222513341787 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139111661053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_55 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82188900557097 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225790615619 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨55, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82188900557097 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225790615619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_56 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82155310895551 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445158920491 / 20000000000000 : ℝ))
      (E := (cell12917 ⟨56, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82155310895551 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445158920491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_57 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41060872164811 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278224824049 / 12500000000000 : ℝ))
      (E := (cell12917 ⟨57, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41060872164811 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (278224824049 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_58 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41044100415961 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225802640349 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨58, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41044100415961 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225802640349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_59 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82054680375197 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225806623497 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨59, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82054680375197 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225806623497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12918_40 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82695533518311 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112807099419 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨40, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82695533518311 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112807099419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_41 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82661594335643 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225618184743 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨41, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82661594335643 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225618184743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_42 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (8262767867591 / 10000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (222562221363 / 10000000000000 : ℝ))
      (E := (cell12918 ⟨42, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (8262767867591 / 10000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (222562221363 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_43 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41296893254791 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445125245113 / 20000000000000 : ℝ))
      (E := (cell12918 ⟨43, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41296893254791 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445125245113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_44 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82559917807279 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225630219163 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨44, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82559917807279 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225630219163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_45 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82526072539771 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225634192823 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨45, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82526072539771 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225634192823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_46 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20623062669493 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556409550909 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨46, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20623062669493 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556409550909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_47 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82458452192943 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112821124821 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨47, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82458452192943 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112821124821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_48 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82424677055889 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (139102891857 / 6250000000000 : ℝ))
      (E := (cell12918 ⟨48, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82424677055889 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (139102891857 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_49 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41195462619081 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556412565347 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨49, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41195462619081 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556412565347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_50 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41178598355627 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112827140501 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨50, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41178598355627 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112827140501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_51 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41161745723401 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112829133359 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨51, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41161745723401 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112829133359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_52 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (16457961883317 / 20000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556415568623 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨52, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (16457961883317 / 20000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556415568623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_53 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (2056403764813 / 2500000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445133260219 / 20000000000000 : ℝ))
      (E := (cell12918 ⟨53, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (2056403764813 / 2500000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445133260219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_54 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82222514946667 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556417570997 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨54, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82222514946667 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556417570997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_55 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (10273612806403 / 12500000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225674337693 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨55, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (10273612806403 / 12500000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225674337693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_56 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82155313078529 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445135668027 / 20000000000000 : ℝ))
      (E := (cell12918 ⟨56, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82155313078529 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445135668027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_57 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (2566304587533 / 3125000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (44513646927 / 2000000000000 : ℝ))
      (E := (cell12918 ⟨57, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (2566304587533 / 3125000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (44513646927 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_58 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82088203591417 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112843176033 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨58, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82088203591417 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112843176033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_59 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82054683422359 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225690352811 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨59, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82054683422359 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225690352811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12919_40 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (10336941379069 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112748970613 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨40, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (10336941379069 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112748970613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_41 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41330796072359 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225501932683 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨41, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41330796072359 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225501932683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_42 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (82627676779411 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445101193561 / 20000000000000 : ℝ))
      (E := (cell12919 ⟨42, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (82627676779411 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445101193561 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_43 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (2581055778347 / 3125000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112754963909 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨43, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (2581055778347 / 3125000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112754963909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_44 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (82559916498419 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556378482247 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨44, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (82559916498419 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556378482247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_45 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (82526071524123 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225517969787 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨45, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (82526071524123 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225517969787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_46 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41246124977567 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556380497389 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨46, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41246124977567 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556380497389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_47 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (5153653235157 / 6250000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (278190748283 / 12500000000000 : ℝ))
      (E := (cell12919 ⟨47, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (5153653235157 / 6250000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (278190748283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_48 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (10303084614683 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225530016623 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨48, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (10303084614683 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225530016623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_49 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (82390925391341 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445106803853 / 20000000000000 : ℝ))
      (E := (cell12919 ⟨49, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (82390925391341 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445106803853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_50 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41178598577819 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225537991519 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨50, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41178598577819 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225537991519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_51 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (8232349218199 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225541989531 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨51, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (8232349218199 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225541989531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_52 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41144905221089 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556386502569 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨52, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41144905221089 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556386502569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_53 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (82256151908121 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225550050523 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨53, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (82256151908121 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225550050523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_54 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41111258275939 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445110809547 / 20000000000000 : ℝ))
      (E := (cell12919 ⟨54, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41111258275939 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445110809547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_55 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (5136806521603 / 6250000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (69548689291 / 3125000000000 : ℝ))
      (E := (cell12919 ⟨55, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (5136806521603 / 6250000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (69548689291 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_56 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (8215531526177 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556390518849 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨56, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (8215531526177 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556390518849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_57 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41060874636359 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556391524481 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨57, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41060874636359 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556391524481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_58 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (16417641270221 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445114012287 / 20000000000000 : ℝ))
      (E := (cell12919 ⟨58, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (16417641270221 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445114012287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_59 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (82054686469679 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556393519953 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨59, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (82054686469679 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556393519953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12920_40 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (20673882136903 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556345420157 / 25000000000000 : ℝ))
      (E := (cell12920 ⟨40, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (20673882136903 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556345420157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_41 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (3306463598183 / 4000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112692838837 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨41, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (3306463598183 / 4000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112692838837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_42 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82627674883659 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225389719067 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨42, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82627674883659 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225389719067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_43 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82593783305339 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (222539374487 / 10000000000000 : ℝ))
      (E := (cell12920 ⟨43, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82593783305339 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (222539374487 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_44 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (16511983038047 / 20000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225397753697 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨44, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (16511983038047 / 20000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225397753697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_45 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41263035254559 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445080348789 / 20000000000000 : ℝ))
      (E := (cell12920 ⟨45, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41263035254559 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445080348789 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_46 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (10311531154113 / 12500000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445081154541 / 20000000000000 : ℝ))
      (E := (cell12920 ⟨46, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (10311531154113 / 12500000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445081154541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_47 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41229225666327 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556352444771 / 25000000000000 : ℝ))
      (E := (cell12920 ⟨47, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41229225666327 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556352444771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_48 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82424676779577 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556353440209 / 25000000000000 : ℝ))
      (E := (cell12920 ⟨48, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82424676779577 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556353440209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_49 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (1287358211641 / 1562500000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225417774479 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨49, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (1287358211641 / 1562500000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225417774479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_50 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (8235719760049 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556355439603 / 25000000000000 : ℝ))
      (E := (cell12920 ⟨50, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (8235719760049 / 10000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556355439603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_51 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82323492917613 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278178221097 / 12500000000000 : ℝ))
      (E := (cell12920 ⟨51, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82323492917613 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278178221097 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_52 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (20572452867043 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (44508596051 / 2000000000000 : ℝ))
      (E := (cell12920 ⟨52, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (20572452867043 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (44508596051 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_53 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82256153224087 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225433797429 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨53, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82256153224087 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225433797429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_54 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (4111125907871 / 5000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445087561799 / 20000000000000 : ℝ))
      (E := (cell12920 ⟨54, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (4111125907871 / 5000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445087561799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_55 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82188906240369 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225441833599 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨55, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82188906240369 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225441833599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_56 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82155317445273 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (27818072603 / 1250000000000 : ℝ))
      (E := (cell12920 ⟨56, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82155317445273 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (27818072603 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_57 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (2566304742019 / 3125000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225449847117 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨57, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (2566304742019 / 3125000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225449847117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_58 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82088209110987 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (34772716057 / 1562500000000 : ℝ))
      (E := (cell12920 ⟨58, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82088209110987 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (34772716057 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_59 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (2051367237929 / 2500000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112728931857 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨59, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (2051367237929 / 2500000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112728931857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12921_40 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82695526063489 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225265475813 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨40, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82695526063489 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225265475813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_41 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41330793882607 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225269478507 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨41, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41330793882607 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225269478507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_42 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (5164229561791 / 6250000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (222527352623 / 10000000000000 : ℝ))
      (E := (cell12921 ⟨42, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (5164229561791 / 6250000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (222527352623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_43 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82593781704287 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445055500041 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨43, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82593781704287 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445055500041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_44 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (8255991388273 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (22252815167 / 1000000000000 : ℝ))
      (E := (cell12921 ⟨44, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (8255991388273 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (22252815167 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_45 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (20631517373689 / 25000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225285515297 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨45, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (20631517373689 / 25000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225285515297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_46 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82492248511281 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445057910617 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨46, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82492248511281 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445057910617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_47 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82458450903369 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (222529356917 / 10000000000000 : ℝ))
      (E := (cell12921 ⟨47, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82458450903369 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (222529356917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_48 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (20606169160557 / 25000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445059512261 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨48, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (20606169160557 / 25000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445059512261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_49 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (8239092569921 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225301586009 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨49, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (8239092569921 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225301586009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_50 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82357198045811 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112652790839 / 50000000000000 : ℝ))
      (E := (cell12921 ⟨50, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82357198045811 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112652790839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_51 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (8232349365367 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445061920891 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨51, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (8232349365367 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445061920891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_52 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (16457962498913 / 20000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225313592269 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨52, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (16457962498913 / 20000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225313592269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_53 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82256154540419 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112658800443 / 50000000000000 : ℝ))
      (E := (cell12921 ⟨53, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82256154540419 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112658800443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_54 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (20555629940823 / 25000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445064325373 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨54, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (20555629940823 / 25000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445064325373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_55 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41094454067693 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445065121487 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨55, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41094454067693 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445065121487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_56 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41077659814519 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445065931391 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨56, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41077659814519 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445065931391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_57 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41060877108363 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445066730619 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨57, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41060877108363 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445066730619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_58 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82088211871063 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (139083603169 / 6250000000000 : ℝ))
      (E := (cell12921 ⟨58, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82088211871063 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (139083603169 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_59 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82054692564799 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225341645307 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨59, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82054692564799 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225341645307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12922_40 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82695523580183 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112574663391 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨40, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82695523580183 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112574663391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_41 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (20665396394159 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225153335183 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨41, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (20665396394159 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225153335183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_42 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82627671094399 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (27814466631 / 1250000000000 : ℝ))
      (E := (cell12922 ⟨42, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82627671094399 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (27814466631 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_43 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (41296890051973 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112580685171 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨43, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (41296890051973 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112580685171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_44 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82559912575901 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112582667863 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨44, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82559912575901 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112582667863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_45 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (16505213696207 / 20000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (222516934273 / 10000000000000 : ℝ))
      (E := (cell12922 ⟨45, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (16505213696207 / 20000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (222516934273 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_46 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (41246123895133 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556293347401 / 25000000000000 : ℝ))
      (E := (cell12922 ⟨46, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (41246123895133 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556293347401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_47 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82458450474657 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225177356521 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨47, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82458450474657 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225177356521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_48 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82424676505417 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (89007254363 / 4000000000000 : ℝ))
      (E := (cell12922 ⟨48, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82424676505417 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (89007254363 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_49 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (823909258539 / 1000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (17801483159 / 800000000000 : ℝ))
      (E := (cell12922 ⟨49, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (823909258539 / 1000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (17801483159 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_50 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82357198491601 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225189402317 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨50, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82357198491601 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225189402317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_51 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (1029043679877 / 1250000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225193437543 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨51, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (1029043679877 / 1250000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225193437543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_52 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (41144906760679 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225197438479 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨52, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (41144906760679 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225197438479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_53 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (20564038964279 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225201401821 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨53, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (20564038964279 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225201401821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_54 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (10277815171187 / 12500000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278150680281 / 12500000000000 : ℝ))
      (E := (cell12922 ⟨54, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (10277815171187 / 12500000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278150680281 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_55 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82188910030699 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225209437939 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨55, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82188910030699 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225209437939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_56 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (16431064362613 / 20000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225213444109 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨56, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (16431064362613 / 20000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225213444109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_57 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82121756689071 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556304364173 / 25000000000000 : ℝ))
      (E := (cell12922 ⟨57, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82121756689071 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556304364173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_58 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (20522053657833 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (445044294283 / 20000000000000 : ℝ))
      (E := (cell12922 ⟨58, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (20522053657833 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (445044294283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_59 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (41027347806299 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225225483801 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨59, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (41027347806299 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225225483801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12923_40 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (16539104219539 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225033174767 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨40, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (16539104219539 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225033174767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_41 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (2066539584721 / 2500000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (139064824307 / 6250000000000 : ℝ))
      (E := (cell12923 ⟨41, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (2066539584721 / 2500000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (139064824307 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_42 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (8262766920089 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112520595317 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨42, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (8262766920089 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112520595317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_43 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41296889252159 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556261294691 / 25000000000000 : ℝ))
      (E := (cell12923 ⟨43, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41296889252159 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556261294691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_44 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (330239645079 / 400000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225049210773 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨44, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (330239645079 / 400000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225049210773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_45 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41263033733979 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112526613121 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨45, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41263033733979 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112526613121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_46 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41246123534929 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112528611677 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨46, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41246123534929 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112528611677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_47 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41229225023259 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225061200071 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨47, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41229225023259 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225061200071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_48 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (10303084546143 / 12500000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (139066575819 / 6250000000000 : ℝ))
      (E := (cell12923 ⟨48, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (10303084546143 / 12500000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (139066575819 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_49 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82390926009093 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112534630029 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨49, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82390926009093 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112534630029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_50 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (4117859946893 / 5000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225073220329 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨50, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (4117859946893 / 5000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225073220329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_51 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (16464699025417 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225077268039 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨51, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (16464699025417 / 20000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225077268039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_52 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (1645796290971 / 2000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112540641067 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨52, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (1645796290971 / 2000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112540641067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_53 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82256157174177 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225085259309 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨53, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82256157174177 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225085259309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_54 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82222522976029 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556272328561 / 25000000000000 : ℝ))
      (E := (cell12923 ⟨54, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82222522976029 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556272328561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_55 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (20547227981577 / 25000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (445018665023 / 20000000000000 : ℝ))
      (E := (cell12923 ⟨55, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (20547227981577 / 25000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (445018665023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_56 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41077661998677 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225097287993 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨56, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41077661998677 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225097287993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_57 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (20530439790411 / 25000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556275329269 / 25000000000000 : ℝ))
      (E := (cell12923 ⟨57, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (20530439790411 / 25000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556275329269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_58 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41044108695897 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556276337243 / 25000000000000 : ℝ))
      (E := (cell12923 ⟨58, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41044108695897 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556276337243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_59 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (20513674665139 / 25000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (445021863997 / 20000000000000 : ℝ))
      (E := (cell12923 ⟨59, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (20513674665139 / 25000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (445021863997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12924_40 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82695518616023 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (556229254943 / 25000000000000 : ℝ))
      (E := (cell12924 ⟨40, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82695518616023 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (556229254943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_41 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41330790600913 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444984207939 / 20000000000000 : ℝ))
      (E := (cell12924 ⟨41, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41330790600913 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444984207939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_42 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82627667308127 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112462523939 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨42, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82627667308127 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112462523939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_43 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41296888452701 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224929043149 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨43, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41296888452701 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224929043149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_44 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (20639977491069 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224933082981 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨44, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (20639977491069 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224933082981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_45 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41263033227761 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224937106953 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨45, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41263033227761 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224937106953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_46 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41246123175029 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112470556623 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨46, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41246123175029 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112470556623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_47 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (1649168992379 / 2000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224945099823 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨47, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (1649168992379 / 2000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224945099823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_48 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82424676233409 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (34764830053 / 1562500000000 : ℝ))
      (E := (cell12924 ⟨48, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82424676233409 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (34764830053 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_49 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (20597731541197 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112476561291 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨49, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (20597731541197 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112476561291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_50 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41178599692293 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (6952990921 / 312500000000 : ℝ))
      (E := (cell12924 ⟨50, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41178599692293 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (6952990921 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_51 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82323495864443 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (556240288743 / 25000000000000 : ℝ))
      (E := (cell12924 ⟨51, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82323495864443 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (556240288743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_52 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82289815576141 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444993024647 / 20000000000000 : ℝ))
      (E := (cell12924 ⟨52, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82289815576141 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444993024647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_53 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (20564039622901 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224969173351 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨53, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (20564039622901 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224969173351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_54 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82222524582893 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444994636751 / 20000000000000 : ℝ))
      (E := (cell12924 ⟨54, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82222524582893 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444994636751 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_55 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82188913822213 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224977150721 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨55, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82188913822213 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224977150721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_56 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (5134707886369 / 6250000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224981188607 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨56, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (5134707886369 / 6250000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224981188607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_57 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (20530440408611 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112492587541 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨57, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (20530440408611 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112492587541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_58 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (1641764403049 / 2000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (278123653023 / 12500000000000 : ℝ))
      (E := (cell12924 ⟨58, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (1641764403049 / 2000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (278123653023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_59 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (641052357099 / 781250000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224993213077 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨59, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (641052357099 / 781250000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224993213077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

end BstLean.Part268
