import BstLean.Part268CellShard31Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13125_40 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82693234707093 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202057184421 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨40, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82693234707093 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202057184421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_41 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82659312060859 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550515308383 / 25000000000000 : ℝ))
      (E := (cell13125 ⟨41, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82659312060859 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550515308383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_42 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82625412915317 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (55051631283 / 2500000000000 : ℝ))
      (E := (cell13125 ⟨42, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82625412915317 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (55051631283 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_43 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41295768620489 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101034618253 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨43, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41295768620489 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101034618253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_44 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (16511537001701 / 20000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202073246477 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨44, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (16511537001701 / 20000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202073246477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_45 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82523856188707 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202077279591 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨45, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82523856188707 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202077279591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_46 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82490050752539 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (275260159383 / 12500000000000 : ℝ))
      (E := (cell13125 ⟨46, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82490050752539 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (275260159383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_47 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82456268671103 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550521322427 / 25000000000000 : ℝ))
      (E := (cell13125 ⟨47, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82456268671103 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550521322427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_48 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82422509915643 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202089321239 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨48, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82422509915643 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202089321239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_49 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (5149298403597 / 6250000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (55052334179 / 2500000000000 : ℝ))
      (E := (cell13125 ⟨49, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (5149298403597 / 6250000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (55052334179 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_50 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82355062268361 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (110104868287 / 5000000000000 : ℝ))
      (E := (cell13125 ⟨50, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82355062268361 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (110104868287 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_51 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41160686659873 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550525343259 / 25000000000000 : ℝ))
      (E := (cell13125 ⟨51, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41160686659873 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550525343259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_52 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (20571926895881 / 25000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101052692959 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨52, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (20571926895881 / 25000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101052692959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_53 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82254065031653 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550527350261 / 25000000000000 : ℝ))
      (E := (cell13125 ⟨53, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82254065031653 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550527350261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_54 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (8222044563623 / 10000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550528353717 / 25000000000000 : ℝ))
      (E := (cell13125 ⟨54, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (8222044563623 / 10000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550528353717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_55 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82186849369493 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202117423631 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨55, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82186849369493 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202117423631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_56 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (16430655240763 / 20000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101060741267 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨56, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (16430655240763 / 20000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101060741267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_57 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (8211972611171 / 10000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202125469101 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨57, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (8211972611171 / 10000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202125469101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_58 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82086199065827 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202129497307 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨58, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82086199065827 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202129497307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_59 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (1641053900779 / 2000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202133503407 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨59, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (1641053900779 / 2000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202133503407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13126_40 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41346610395641 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201945684709 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨40, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41346610395641 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201945684709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_41 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82659298151123 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100974865849 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨41, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82659298151123 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100974865849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_42 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (1652507980233 / 2000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220195374741 / 10000000000000 : ℝ))
      (E := (cell13126 ⟨42, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (1652507980233 / 2000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220195374741 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_43 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (5161970208961 / 6250000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201957730567 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨43, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (5161970208961 / 6250000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201957730567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_44 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41278835558481 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550490449359 / 25000000000000 : ℝ))
      (E := (cell13126 ⟨44, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41278835558481 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550490449359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_45 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82523842303219 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201965769731 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨45, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82523842303219 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201965769731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_46 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82490036873101 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100984911121 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨46, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82490036873101 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100984911121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_47 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82456254797709 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275246729383 / 12500000000000 : ℝ))
      (E := (cell13126 ⟨47, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82456254797709 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275246729383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_48 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (8242249604829 / 10000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550494451461 / 25000000000000 : ℝ))
      (E := (cell13126 ⟨48, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (8242249604829 / 10000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550494451461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_49 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82388760596233 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201981850013 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨49, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82388760596233 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201981850013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_50 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (5147190525817 / 6250000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100992923443 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨50, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (5147190525817 / 6250000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100992923443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_51 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41160679735241 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (137624369473 / 6250000000000 : ℝ))
      (E := (cell13126 ⟨51, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41160679735241 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (137624369473 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_52 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82287693740281 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201993922857 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨52, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82287693740281 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201993922857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_53 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41127025597213 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100998968219 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨53, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41127025597213 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100998968219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_54 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41110215902507 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1101000974381 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨54, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41110215902507 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1101000974381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_55 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82186835544283 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2202005956071 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨55, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82186835544283 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2202005956071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_56 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82153262384607 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2202009954403 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨56, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82153262384607 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2202009954403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_57 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82119712298499 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550503499693 / 25000000000000 : ℝ))
      (E := (cell13126 ⟨57, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82119712298499 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550503499693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_58 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82086185258607 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2202018025663 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨58, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82086185258607 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2202018025663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_59 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82052681237717 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2202022030493 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨59, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82052681237717 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2202022030493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13127_40 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41346603438797 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201834239569 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨40, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41346603438797 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201834239569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_41 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (20664821060877 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201838225651 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨41, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (20664821060877 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201838225651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_42 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (10328173138763 / 12500000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (275230279911 / 12500000000000 : ℝ))
      (E := (cell13127 ⟨42, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (10328173138763 / 12500000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (275230279911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_43 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82591509447893 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100923139637 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨43, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82591509447893 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100923139637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_44 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82557657227539 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100925142651 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨44, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82557657227539 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100925142651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_45 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82523828419849 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100927157283 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨45, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82523828419849 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100927157283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_46 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82490022995779 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100929153141 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨46, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82490022995779 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100929153141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_47 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (2576757528951 / 3125000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201862317259 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨47, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (2576757528951 / 3125000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201862317259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_48 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82422482183051 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201866345217 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨48, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82422482183051 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201866345217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_49 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82388746737029 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (275233798457 / 12500000000000 : ℝ))
      (E := (cell13127 ⟨49, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82388746737029 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (275233798457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_50 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82355034559897 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (134391747 / 6103515625 : ℝ))
      (E := (cell13127 ⟨50, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82355034559897 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (134391747 / 6103515625 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_51 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (20580336405833 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100939193423 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨51, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (20580336405833 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100939193423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_52 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (1645753597983 / 2000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201882455591 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨52, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (1645753597983 / 2000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201882455591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_53 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (8225403735931 / 10000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201886467627 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨53, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (8225403735931 / 10000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201886467627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_54 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82220417975909 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (550472619613 / 25000000000000 : ℝ))
      (E := (cell13127 ⟨54, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82220417975909 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (550472619613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_55 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41093410860591 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (220189448431 / 10000000000000 : ℝ))
      (E := (cell13127 ⟨55, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41093410860591 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (220189448431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_56 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82153248567507 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100949240617 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨56, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82153248567507 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100949240617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_57 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41059849243697 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201902524243 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨57, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41059849243697 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201902524243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_58 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41043085726747 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100953274909 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨58, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41043085726747 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100953274909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_59 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82052667438591 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100955276689 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨59, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82052667438591 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100955276689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13128_40 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (20673298241507 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (440344558043 / 20000000000000 : ℝ))
      (E := (cell13128 ⟨40, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (20673298241507 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (440344558043 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_41 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (16531854067603 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (11008633871 / 500000000000 : ℝ))
      (E := (cell13128 ⟨41, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (16531854067603 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (11008633871 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_42 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (41312685605339 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201730785787 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨42, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (41312685605339 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201730785787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_43 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (82591495554531 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (275216852971 / 12500000000000 : ℝ))
      (E := (cell13128 ⟨43, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (82591495554531 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (275216852971 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_44 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (41278821670117 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100869413919 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨44, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (41278821670117 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100869413919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_45 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (82523814538597 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (220174285519 / 10000000000000 : ℝ))
      (E := (cell13128 ⟨45, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (82523814538597 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (220174285519 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_46 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (3299600364823 / 4000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201746903969 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨46, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (3299600364823 / 4000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201746903969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_47 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (8245622705727 / 10000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (44035018263 / 2000000000000 : ℝ))
      (E := (cell13128 ⟨47, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (8245622705727 / 10000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (44035018263 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_48 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (10302808539991 / 12500000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100877440191 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨48, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (10302808539991 / 12500000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100877440191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_49 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (82388732879939 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201758921093 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨49, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (82388732879939 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201758921093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_50 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (16471004141767 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550440728651 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨50, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (16471004141767 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550440728651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_51 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (41160665889147 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201766976011 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨51, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (41160665889147 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201766976011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_52 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (82287666060131 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201770984121 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨52, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (82287666060131 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201770984121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_53 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (16450804705261 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201774994613 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨53, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (16450804705261 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201774994613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_54 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (5138775259307 / 6250000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201779003941 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨54, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (5138775259307 / 6250000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201779003941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_55 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (8218680790019 / 10000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100891504173 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨55, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (8218680790019 / 10000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100891504173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_56 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (16430646950503 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201787063027 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨56, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (16430646950503 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201787063027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_57 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (82119684678397 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201791045513 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨57, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (82119684678397 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201791045513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_58 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (41043078825243 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (88071802791 / 4000000000000 : ℝ))
      (E := (cell13128 ⟨58, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (41043078825243 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (88071802791 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_59 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (82052653641569 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (22017991313 / 1000000000000 : ℝ))
      (E := (cell13128 ⟨59, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (82052653641569 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (22017991313 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13129_40 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (10336647382073 / 12500000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (44032226733 / 2000000000000 : ℝ))
      (E := (cell13129 ⟨40, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (10336647382073 / 12500000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (44032226733 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_41 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82659256434643 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (44032307547 / 2000000000000 : ℝ))
      (E := (cell13129 ⟨41, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82659256434643 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (44032307547 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_42 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82625357313373 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201619386911 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨42, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82625357313373 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201619386911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_43 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82591481663287 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201623422913 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨43, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82591481663287 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201623422913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_44 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82557629455047 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201627425049 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨44, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82557629455047 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201627425049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_45 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (41261900329731 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201631450513 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨45, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (41261900329731 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201631450513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_46 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82489995247487 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201635438521 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨46, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82489995247487 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201635438521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_47 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (5153513324389 / 6250000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550409861471 / 25000000000000 : ℝ))
      (E := (cell13129 ⟨47, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (5153513324389 / 6250000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550409861471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_48 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82422454458919 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100821735159 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨48, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82422454458919 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100821735159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_49 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (41194359512481 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201647509327 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨49, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (41194359512481 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201647509327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_50 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (41177503429943 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201651501179 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨50, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (41177503429943 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201651501179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_51 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82321317935367 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (220165550193 / 10000000000000 : ℝ))
      (E := (cell13129 ⟨51, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82321317935367 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (220165550193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_52 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (41143826111611 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (13760372297 / 625000000000 : ℝ))
      (E := (cell13129 ⟨52, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (41143826111611 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (13760372297 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_53 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82254009695409 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550415894123 / 25000000000000 : ℝ))
      (E := (cell13129 ⟨53, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82254009695409 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550415894123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_54 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (3288815612961 / 4000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100833792173 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨54, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (3288815612961 / 4000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100833792173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_55 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (41093397040653 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550417896831 / 25000000000000 : ℝ))
      (E := (cell13129 ⟨55, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (41093397040653 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550417896831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_56 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82153220939629 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (137604727539 / 6250000000000 : ℝ))
      (E := (cell13129 ⟨56, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82153220939629 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (137604727539 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_57 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (16423934174301 / 20000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100839810887 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨57, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (16423934174301 / 20000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100839810887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_58 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (5130383990599 / 6250000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (440336728949 / 20000000000000 : ℝ))
      (E := (cell13129 ⟨58, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (5130383990599 / 6250000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (440336728949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_59 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82052639846651 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201687645793 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨59, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82052639846651 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201687645793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13130_40 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41346582574631 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201499937659 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨40, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41346582574631 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201499937659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_41 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82659242533391 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201503976289 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨41, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82659242533391 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201503976289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_42 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82625343418187 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137594248989 / 6250000000000 : ℝ))
      (E := (cell13130 ⟨42, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82625343418187 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137594248989 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_43 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41295733887081 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (550377989747 / 25000000000000 : ℝ))
      (E := (cell13130 ⟨43, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41295733887081 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (550377989747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_44 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82557615571977 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (44030320361 / 2000000000000 : ℝ))
      (E := (cell13130 ⟨44, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82557615571977 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (44030320361 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_45 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82523786782443 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (550380010407 / 25000000000000 : ℝ))
      (E := (cell13130 ⟨45, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82523786782443 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (550380010407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_46 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (16497996275303 / 20000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100762013897 / 50000000000000 : ℝ))
      (E := (cell13130 ⟨46, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (16497996275303 / 20000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100762013897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_47 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82456199325293 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100764016681 / 50000000000000 : ℝ))
      (E := (cell13130 ⟨47, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82456199325293 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100764016681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_48 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (10302805075003 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137595753503 / 6250000000000 : ℝ))
      (E := (cell13130 ⟨48, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (10302805075003 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137595753503 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_49 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82388705172099 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201536093353 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨49, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82388705172099 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201536093353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_50 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82354993013049 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201540083549 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨50, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82354993013049 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201540083549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_51 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (10290163011819 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (275193017717 / 12500000000000 : ℝ))
      (E := (cell13130 ⟨51, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (10290163011819 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (275193017717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_52 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (10285954798553 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440309629343 / 20000000000000 : ℝ))
      (E := (cell13130 ⟨52, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (10285954798553 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440309629343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_53 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82253995866623 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201552154169 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨53, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82253995866623 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201552154169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_54 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41110188250623 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (44031123211 / 2000000000000 : ℝ))
      (E := (cell13130 ⟨54, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41110188250623 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (44031123211 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_55 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (8218678026453 / 10000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201560162101 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨55, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (8218678026453 / 10000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201560162101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_56 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82153207128851 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (110078210701 / 5000000000000 : ℝ))
      (E := (cell13130 ⟨56, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82153207128851 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (110078210701 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_57 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (513247856667 / 625000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100784126511 / 50000000000000 : ℝ))
      (E := (cell13130 ⟨57, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (513247856667 / 625000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100784126511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_58 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82086130050787 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (275196534341 / 12500000000000 : ℝ))
      (E := (cell13130 ⟨58, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82086130050787 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (275196534341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_59 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82052626053837 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201576274557 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨59, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82052626053837 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201576274557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13131_40 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (4134657562203 / 5000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201388534459 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨40, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (4134657562203 / 5000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201388534459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_41 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (4132961431713 / 5000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201392571017 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨41, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (4132961431713 / 5000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201392571017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_42 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (129102077383 / 156250000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201396576529 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨42, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (129102077383 / 156250000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201396576529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_43 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (16518290777431 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201400608573 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨43, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (16518290777431 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201400608573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_44 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (3302304067641 / 4000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440280921369 / 20000000000000 : ℝ))
      (E := (cell13131 ⟨44, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (3302304067641 / 4000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440280921369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_45 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (82523772907541 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (275176078567 / 12500000000000 : ℝ))
      (E := (cell13131 ⟨45, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (82523772907541 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (275176078567 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_46 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41244983753829 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100706306431 / 50000000000000 : ℝ))
      (E := (cell13131 ⟨46, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41244983753829 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100706306431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_47 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (20614046365619 / 25000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201416675589 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨47, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (20614046365619 / 25000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201416675589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_48 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (82422426743243 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (44028413931 / 2000000000000 : ℝ))
      (E := (cell13131 ⟨48, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (82422426743243 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (44028413931 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_49 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (20597172830337 / 25000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100712336589 / 50000000000000 : ℝ))
      (E := (cell13131 ⟨49, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (20597172830337 / 25000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100712336589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_50 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (20588744792081 / 25000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201428720741 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨50, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (20588744792081 / 25000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201428720741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_51 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (10290161281981 / 12500000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440286543659 / 20000000000000 : ℝ))
      (E := (cell13131 ⟨51, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (10290161281981 / 12500000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440286543659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_52 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (10285953069467 / 12500000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (220143672171 / 10000000000000 : ℝ))
      (E := (cell13131 ⟨52, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (10285953069467 / 12500000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (220143672171 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_53 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (16450796407989 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (110072039337 / 5000000000000 : ℝ))
      (E := (cell13131 ⟨53, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (16450796407989 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (110072039337 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_54 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (3288814507223 / 4000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201444791673 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨54, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (3288814507223 / 4000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201444791673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_55 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (82186766449861 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201448791821 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨55, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (82186766449861 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201448791821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_56 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41076596660089 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440290568477 / 20000000000000 : ℝ))
      (E := (cell13131 ⟨56, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41076596660089 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440290568477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_57 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (2052991081601 / 2500000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (275182102611 / 12500000000000 : ℝ))
      (E := (cell13131 ⟨57, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (2052991081601 / 2500000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (275182102611 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_58 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41043058127047 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100730420653 / 50000000000000 : ℝ))
      (E := (cell13131 ⟨58, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41043058127047 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100730420653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_59 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (82052612263127 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201464899127 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨59, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (82052612263127 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201464899127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13132_40 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82693137340979 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100638592919 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨40, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82693137340979 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100638592919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_41 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82659214737247 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100640580769 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨41, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82659214737247 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100640580769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_42 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (20656328908543 / 25000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201285223861 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨42, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (20656328908543 / 25000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201285223861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_43 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16518288000453 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201289195093 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨43, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16518288000453 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201289195093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_44 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (8255758781219 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440258650063 / 20000000000000 : ℝ))
      (E := (cell13132 ⟨44, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (8255758781219 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440258650063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_45 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16504751806951 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (17197634923 / 781250000000 : ℝ))
      (E := (cell13132 ⟨45, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16504751806951 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (17197634923 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_46 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (20622488410229 / 25000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440260250531 / 20000000000000 : ℝ))
      (E := (cell13132 ⟨46, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (20622488410229 / 25000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440260250531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_47 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82456171601773 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201305313613 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨47, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82456171601773 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201305313613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_48 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (41211206444287 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201309332851 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨48, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (41211206444287 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201309332851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_49 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82388677472709 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201313307801 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨49, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82388677472709 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201313307801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_50 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (8235496532571 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550329338433 / 25000000000000 : ℝ))
      (E := (cell13132 ⟨50, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (8235496532571 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550329338433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_51 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82321276419253 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201321349701 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨51, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82321276419253 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201321349701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_52 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (20571902681289 / 25000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201325351577 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨52, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (20571902681289 / 25000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201325351577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_53 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (5140873013461 / 6250000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201329415113 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨53, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (5140873013461 / 6250000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201329415113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_54 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82220348862011 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100666709299 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨54, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82220348862011 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100666709299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_55 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (41093376318649 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440267483469 / 20000000000000 : ℝ))
      (E := (cell13132 ⟨55, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (41093376318649 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440267483469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_56 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82153179513611 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201341466553 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨56, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82153179513611 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201341466553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_57 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (10264953682933 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201345443747 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨57, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (10264953682933 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201345443747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_58 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16417220491901 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201349462901 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨58, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16417220491901 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201349462901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_59 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (2051314961863 / 2500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201353519503 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨59, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (2051314961863 / 2500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201353519503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13133_40 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41346561720009 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201165833007 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨40, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41346561720009 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201165833007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_41 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41329600421177 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100584932737 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨41, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41329600421177 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100584932737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_42 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82625301745341 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100586933493 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨42, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82625301745341 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100586933493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_43 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82591426119493 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550294473781 / 25000000000000 : ℝ))
      (E := (cell13133 ⟨43, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82591426119493 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550294473781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_44 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82557573935471 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (110059094479 / 5000000000000 : ℝ))
      (E := (cell13133 ⟨44, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82557573935471 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (110059094479 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_45 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (20630936291021 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201185907549 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨45, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (20630936291021 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201185907549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_46 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (2577810618009 / 3125000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100594973587 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨46, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (2577810618009 / 3125000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100594973587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_47 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (5153509858949 / 6250000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100596973717 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨47, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (5153509858949 / 6250000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100596973717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_48 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82422399036019 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550299491237 / 25000000000000 : ℝ))
      (E := (cell13133 ⟨48, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82422399036019 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550299491237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_49 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41194331813091 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100600998611 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨49, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41194331813091 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100600998611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_50 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82354951485207 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100602991261 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨50, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82354951485207 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100602991261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_51 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82321262584769 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201210035953 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨51, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82321262584769 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201210035953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_52 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41143798448343 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100607018157 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨52, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41143798448343 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100607018157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_53 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (20563488598229 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275152254911 / 12500000000000 : ℝ))
      (E := (cell13133 ⟨53, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (20563488598229 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275152254911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_54 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (16444067009111 / 20000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201222041327 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨54, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (16444067009111 / 20000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201222041327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_55 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82186738826841 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201226097813 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨55, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82186738826841 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201226097813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_56 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (1643063314183 / 2000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100615043263 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨56, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (1643063314183 / 2000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100615043263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_57 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82119615664993 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100617060799 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨57, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82119615664993 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100617060799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_58 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82086088667019 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201238139513 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨58, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82086088667019 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201238139513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_59 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (16410516937603 / 20000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275155266961 / 12500000000000 : ℝ))
      (E := (cell13133 ⟨59, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (16410516937603 / 20000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275155266961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13134_40 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10336638692647 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201054475969 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨40, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10336638692647 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201054475969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_41 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (4132959347479 / 5000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (220105850639 / 10000000000000 : ℝ))
      (E := (cell13134 ⟨41, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (4132959347479 / 5000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (220105850639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_42 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (82625287858629 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (137566406619 / 6250000000000 : ℝ))
      (E := (cell13134 ⟨42, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (82625287858629 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (137566406619 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_43 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41295706119419 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (220106653209 / 10000000000000 : ℝ))
      (E := (cell13134 ⟨43, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41295706119419 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (220106653209 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_44 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (20639390015217 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100535291761 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨44, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (20639390015217 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100535291761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_45 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10315466411941 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100537299827 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨45, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10315466411941 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100537299827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_46 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41244962956887 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201078578561 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨46, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41244962956887 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201078578561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_47 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (20614035971677 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (550270659001 / 25000000000000 : ℝ))
      (E := (cell13134 ⟨47, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (20614035971677 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (550270659001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_48 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (3296895407423 / 4000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201086651821 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨48, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (3296895407423 / 4000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201086651821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_49 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41194324890883 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201090623443 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨49, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41194324890883 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201090623443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_50 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41177468823407 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275136833267 / 12500000000000 : ℝ))
      (E := (cell13134 ⟨50, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41177468823407 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275136833267 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_51 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41160624376197 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201098658961 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨51, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41160624376197 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201098658961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_52 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (20571895767581 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100551358427 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨52, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (20571895767581 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100551358427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_53 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41126970286281 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201106718359 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨53, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41126970286281 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201106718359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_54 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (16444064246241 / 20000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (4299044373 / 195312500000 : ℝ))
      (E := (cell13134 ⟨54, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (16444064246241 / 20000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (4299044373 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_55 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (82186725018491 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (440222954817 / 20000000000000 : ℝ))
      (E := (cell13134 ⟨55, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (82186725018491 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (440222954817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_56 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (82153151906793 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (550279690367 / 25000000000000 : ℝ))
      (E := (cell13134 ⟨56, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (82153151906793 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (550279690367 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_57 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (656956814949 / 800000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275140349407 / 12500000000000 : ℝ))
      (E := (cell13134 ⟨57, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (656956814949 / 800000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275140349407 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_58 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (20521518719159 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (550281702983 / 25000000000000 : ℝ))
      (E := (cell13134 ⟨58, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (20521518719159 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (550281702983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_59 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (20513142725903 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100565403457 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨59, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (20513142725903 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100565403457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13135_40 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41346547822227 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275117896689 / 12500000000000 : ℝ))
      (E := (cell13135 ⟨40, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41346547822227 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275117896689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_41 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82659173058923 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440189440383 / 20000000000000 : ℝ))
      (E := (cell13135 ⟨41, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82659173058923 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440189440383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_42 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82625273974033 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440190239891 / 20000000000000 : ℝ))
      (E := (cell13135 ⟨42, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82625273974033 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440190239891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_43 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41295699180149 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (68779850741 / 3125000000000 : ℝ))
      (E := (cell13135 ⟨43, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41295699180149 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (68779850741 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_44 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82557546188379 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200959273263 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨44, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82557546188379 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200959273263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_45 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41261858714543 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200963287559 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨45, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41261858714543 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200963287559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_46 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41244956026687 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (88038690587 / 4000000000000 : ℝ))
      (E := (cell13135 ⟨46, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41244956026687 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (88038690587 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_47 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (10307016254043 / 12500000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275121415047 / 12500000000000 : ℝ))
      (E := (cell13135 ⟨47, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (10307016254043 / 12500000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275121415047 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_48 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82422371337243 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440195066899 / 20000000000000 : ℝ))
      (E := (cell13135 ⟨48, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82422371337243 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440195066899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_49 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (4119431796973 / 5000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440195872693 / 20000000000000 : ℝ))
      (E := (cell13135 ⟨49, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (4119431796973 / 5000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440195872693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_50 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (8235492381053 / 10000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100491672777 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨50, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (8235492381053 / 10000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100491672777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_51 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (5145077182633 / 6250000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440197479173 / 20000000000000 : ℝ))
      (E := (cell13135 ⟨51, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (5145077182633 / 6250000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440197479173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_52 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (8228756924607 / 10000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100495696599 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨52, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (8228756924607 / 10000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100495696599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_53 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (20563481688579 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550248848309 / 25000000000000 : ℝ))
      (E := (cell13135 ⟨53, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (20563481688579 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550248848309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_54 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41110153709481 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200999451547 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨54, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41110153709481 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200999451547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_55 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (16437342242449 / 20000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440200689233 / 20000000000000 : ℝ))
      (E := (cell13135 ⟨55, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (16437342242449 / 20000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440200689233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_56 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (4107656905327 / 5000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2201007491383 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨56, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (4107656905327 / 5000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2201007491383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_57 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82119588074361 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2201011464723 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨57, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82119588074361 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2201011464723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_58 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (20521515272089 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2201015480161 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨58, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (20521515272089 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2201015480161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_59 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (8205255712131 / 10000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100509766593 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨59, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (8205255712131 / 10000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100509766593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13136_40 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (82693081749849 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200831925639 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨40, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (82693081749849 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200831925639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_41 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (5166197448149 / 6250000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (137552243327 / 6250000000000 : ℝ))
      (E := (cell13136 ⟨41, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (5166197448149 / 6250000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (137552243327 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_42 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41312630045777 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440167989527 / 20000000000000 : ℝ))
      (E := (cell13136 ⟨42, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41312630045777 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440167989527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_43 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (660731075871 / 800000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550210992497 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨43, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (660731075871 / 800000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550210992497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_44 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41278766159003 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200847958799 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨44, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41278766159003 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200847958799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_45 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41261851782379 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200851971261 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨45, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41261851782379 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200851971261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_46 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41244949097543 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100428002759 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨46, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41244949097543 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100428002759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_47 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20614029045023 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200860000547 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨47, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20614029045023 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200860000547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_48 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41211178745511 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275108001621 / 12500000000000 : ℝ))
      (E := (cell13136 ⟨48, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41211178745511 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275108001621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_49 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (16477724419853 / 20000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (68777126259 / 3125000000000 : ℝ))
      (E := (cell13136 ⟨49, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (16477724419853 / 20000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (68777126259 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_50 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20588727494089 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550218019949 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨50, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20588727494089 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550218019949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_51 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (8232122109397 / 10000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (88035042781 / 4000000000000 : ℝ))
      (E := (cell13136 ⟨51, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (8232122109397 / 10000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (88035042781 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_52 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20571888855981 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440176024883 / 20000000000000 : ℝ))
      (E := (cell13136 ⟨52, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20571888855981 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440176024883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_53 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (1285217389659 / 1562500000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (220088412301 / 10000000000000 : ℝ))
      (E := (cell13136 ⟨53, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (1285217389659 / 1562500000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (220088412301 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_54 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (82220293608823 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200888120809 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨54, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (82220293608823 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200888120809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_55 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (10273337176013 / 12500000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200892173191 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨55, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (10273337176013 / 12500000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200892173191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_56 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (10269140538549 / 12500000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200896157939 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨56, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (10269140538549 / 12500000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200896157939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_57 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (410597871411 / 500000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2149316591 / 97656250000 : ℝ))
      (E := (cell13136 ⟨57, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (410597871411 / 500000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2149316591 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_58 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41043023651089 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200904203409 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨58, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41043023651089 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200904203409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_59 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (8205254334111 / 10000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200908255267 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨59, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (8205254334111 / 10000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200908255267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13137_40 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82693067857363 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (550180153693 / 25000000000000 : ℝ))
      (E := (cell13137 ⟨40, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82693067857363 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (550180153693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_41 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41329572641981 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200724639159 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨41, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41329572641981 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200724639159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_42 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (10328155776399 / 12500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (550182172903 / 25000000000000 : ℝ))
      (E := (cell13137 ⟨42, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (10328155776399 / 12500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (550182172903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_43 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41295685304783 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440146530641 / 20000000000000 : ℝ))
      (E := (cell13137 ⟨43, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41295685304783 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440146530641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_44 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82557518449747 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100368349509 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨44, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82557518449747 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100368349509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_45 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (5157730606409 / 6250000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200740709669 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨45, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (5157730606409 / 6250000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200740709669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_46 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82489884338911 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100372371081 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨46, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82489884338911 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100372371081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_47 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (2576753197811 / 3125000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (137546795967 / 6250000000000 : ℝ))
      (E := (cell13137 ⟨47, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (2576753197811 / 3125000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (137546795967 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_48 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82422343646911 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100376373111 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨48, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82422343646911 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100376373111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_49 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (4119430413059 / 5000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440151354383 / 20000000000000 : ℝ))
      (E := (cell13137 ⟨49, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (4119430413059 / 5000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440151354383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_50 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82354896144291 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100380404921 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨50, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82354896144291 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100380404921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_51 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (1029015090849 / 1250000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200764798037 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨51, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (1029015090849 / 1250000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200764798037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_52 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (20571885400971 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (27509610643 / 1250000000000 : ℝ))
      (E := (cell13137 ⟨52, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (20571885400971 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (27509610643 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_53 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41126949562071 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200772848593 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨53, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41126949562071 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200772848593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_54 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (8222027980079 / 10000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200776904111 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨54, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (8222027980079 / 10000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200776904111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_55 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82186683606067 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200780896027 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨55, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82186683606067 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200780896027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_56 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41076555256173 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100392469317 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨56, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41076555256173 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100392469317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_57 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82119560492141 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (137549306841 / 6250000000000 : ℝ))
      (E := (cell13137 ⟨57, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82119560492141 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (137549306841 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_58 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82086033518101 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200792922469 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨58, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82086033518101 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200792922469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_59 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (8205252956301 / 10000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (55019924329 / 2500000000000 : ℝ))
      (E := (cell13137 ⟨59, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (8205252956301 / 10000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (55019924329 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13138_40 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41346526983497 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (220060935849 / 10000000000000 : ℝ))
      (E := (cell13138 ⟨40, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41346526983497 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (220060935849 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_41 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (10332391424957 / 12500000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550153345221 / 25000000000000 : ℝ))
      (E := (cell13138 ⟨41, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (10332391424957 / 12500000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550153345221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_42 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (5164077020809 / 6250000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200617431389 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨42, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (5164077020809 / 6250000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200617431389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_43 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (20647839184343 / 25000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200621449939 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨43, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (20647839184343 / 25000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200621449939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_44 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41278752291801 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550156358759 / 25000000000000 : ℝ))
      (E := (cell13138 ⟨44, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41278752291801 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550156358759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_45 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41261837921221 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100314721939 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨45, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41261837921221 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100314721939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_46 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (5155616905303 / 6250000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200633474607 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨46, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (5155616905303 / 6250000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200633474607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_47 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82456088481923 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (68769922661 / 3125000000000 : ℝ))
      (E := (cell13138 ⟨47, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82456088481923 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (68769922661 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_48 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82422329804911 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440128306851 / 20000000000000 : ℝ))
      (E := (cell13138 ⟨48, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82422329804911 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440128306851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_49 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82388594425203 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100322779173 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨49, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82388594425203 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100322779173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_50 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82354882314333 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100324767847 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨50, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82354882314333 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100324767847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_51 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82321193443977 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100326790701 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨51, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82321193443977 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100326790701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_52 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82287527785951 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200657574271 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨52, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82287527785951 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200657574271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_53 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82253885312213 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550165407269 / 25000000000000 : ℝ))
      (E := (cell13138 ⟨53, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82253885312213 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550165407269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_54 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41110132997431 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440133124821 / 20000000000000 : ℝ))
      (E := (cell13138 ⟨54, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41110132997431 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440133124821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_55 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41093334903067 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550167418453 / 25000000000000 : ℝ))
      (E := (cell13138 ⟨55, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41093334903067 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550167418453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_56 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82153096718403 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (88026946239 / 4000000000000 : ℝ))
      (E := (cell13138 ⟨56, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82153096718403 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (88026946239 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_57 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (10264943338023 / 12500000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200677684727 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨57, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (10264943338023 / 12500000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200677684727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_58 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (656688157889 / 800000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200681696551 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨58, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (656688157889 / 800000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200681696551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_59 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82052515787011 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (22006857461 / 1000000000000 : ℝ))
      (E := (cell13138 ⟨59, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82052515787011 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (22006857461 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13139_40 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (41346520039371 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100249078397 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨40, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (41346520039371 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100249078397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_41 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82659117517467 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200502177217 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨41, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82659117517467 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200502177217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_42 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20656304614203 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550126541741 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨42, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20656304614203 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550126541741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_43 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82591342867293 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550127545903 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨43, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82591342867293 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550127545903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_44 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (8255749071957 / 10000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200514225737 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨44, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (8255749071957 / 10000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200514225737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_45 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82523661984453 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200518232793 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨45, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82523661984453 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200518232793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_46 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82489856632897 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200522261783 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨46, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82489856632897 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200522261783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_47 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20614018659001 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200526251683 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨47, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20614018659001 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200526251683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_48 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (4121115798251 / 5000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200530318091 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨48, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (4121115798251 / 5000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200530318091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_49 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (10298572573917 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200534340581 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨49, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (10298572573917 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200534340581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_50 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20588717121621 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100269158187 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨50, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20588717121621 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100269158187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_51 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82321179622141 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200542360573 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨51, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82321179622141 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200542360573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_52 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20571878492531 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100273175989 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨52, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20571878492531 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100273175989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_53 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (8225387150239 / 10000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200550405367 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨53, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (8225387150239 / 10000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200550405367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_54 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (41110126095519 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (137534649939 / 6250000000000 : ℝ))
      (E := (cell13139 ⟨54, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (41110126095519 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (137534649939 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_55 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (5136666000519 / 6250000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100279223703 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨55, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (5136666000519 / 6250000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100279223703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_56 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82153082926563 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (220056242829 / 10000000000000 : ℝ))
      (E := (cell13139 ⟨56, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82153082926563 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (220056242829 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_57 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (10264941614791 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (220056645581 / 10000000000000 : ℝ))
      (E := (cell13139 ⟨57, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (10264941614791 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (220056645581 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_58 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82086005956249 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100285233223 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨58, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82086005956249 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100285233223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_59 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82052502013111 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550143628713 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨59, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82052502013111 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550143628713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13140_40 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82693026192607 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200386950897 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨40, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82693026192607 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200386950897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_41 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82659103637393 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (275048871169 / 12500000000000 : ℝ))
      (E := (cell13140 ⟨41, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82659103637393 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (275048871169 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_42 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (16525040916559 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (220039501601 / 10000000000000 : ℝ))
      (E := (cell13140 ⟨42, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (16525040916559 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (220039501601 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_43 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82591328999327 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100199515403 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨43, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82591328999327 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100199515403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_44 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82557476857651 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200403012241 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨44, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82557476857651 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200403012241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_45 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (3300945925143 / 4000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200407017513 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨45, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (3300945925143 / 4000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200407017513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_46 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (5155615173941 / 6250000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440082208953 / 20000000000000 : ℝ))
      (E := (cell13140 ⟨46, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (5155615173941 / 6250000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440082208953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_47 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (16491212158439 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (88016603677 / 4000000000000 : ℝ))
      (E := (cell13140 ⟨47, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (16491212158439 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (88016603677 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_48 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82422302127239 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200419097733 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨48, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82422302127239 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200419097733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_49 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82388566759577 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100211559311 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨49, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82388566759577 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100211559311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_50 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (41177427330371 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440085430377 / 20000000000000 : ℝ))
      (E := (cell13140 ⟨50, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (41177427330371 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440085430377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_51 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (20580291450603 / 25000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200431135553 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨51, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (20580291450603 / 25000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200431135553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_52 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (41143750078201 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100217592283 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨52, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (41143750078201 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100217592283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_53 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82253857694671 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (550109794367 / 25000000000000 : ℝ))
      (E := (cell13140 ⟨53, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82253857694671 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (550109794367 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_54 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82220238389317 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440088633951 / 20000000000000 : ℝ))
      (E := (cell13140 ⟨54, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82220238389317 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440088633951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_55 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (2568332569143 / 3125000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100223608407 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨55, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (2568332569143 / 3125000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100223608407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_56 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (10269133642103 / 12500000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200451255583 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨56, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (10269133642103 / 12500000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200451255583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_57 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (41059759567287 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (550113820473 / 25000000000000 : ℝ))
      (E := (cell13140 ⟨57, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (41059759567287 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (550113820473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_58 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (41042996089237 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100229645683 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨58, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (41042996089237 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100229645683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_59 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (8205248824131 / 10000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200463279421 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨59, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (8205248824131 / 10000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200463279421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13141_40 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20673253077147 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (687586169 / 31250000000 : ℝ))
      (E := (cell13141 ⟨40, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20673253077147 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (687586169 / 31250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_41 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41329544879717 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200279757287 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨41, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41329544879717 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200279757287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_42 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20656297677723 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200283802023 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨42, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20656297677723 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200283802023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_43 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (3303652605339 / 4000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100143907471 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨43, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (3303652605339 / 4000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100143907471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_44 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20639365749461 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200291853431 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨44, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20639365749461 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200291853431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_45 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (82523634274809 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200295856943 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨45, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (82523634274809 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200295856943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_46 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41244914467663 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (27503748531 / 1250000000000 : ℝ))
      (E := (cell13141 ⟨46, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41244914467663 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (27503748531 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_47 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (2576751467203 / 3125000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200303869019 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨47, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (2576751467203 / 3125000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200303869019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_48 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41211144145783 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100153966079 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨48, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41211144145783 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100153966079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_49 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (3295542117197 / 4000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (137519496967 / 6250000000000 : ℝ))
      (E := (cell13141 ⟨49, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (3295542117197 / 4000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (137519496967 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_50 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (82354840837107 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200315924181 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨50, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (82354840837107 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200315924181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_51 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20580287996197 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200319965389 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨51, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20580287996197 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200319965389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_52 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (16457497268957 / 20000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100161976947 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨52, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (16457497268957 / 20000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100161976947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_53 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (82253843889057 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200328004473 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨53, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (82253843889057 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200328004473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_54 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (822202245897 / 1000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (440066399083 / 20000000000000 : ℝ))
      (E := (cell13141 ⟨54, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (822202245897 / 1000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (440066399083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_55 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (10273328552369 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200336041173 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨55, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (10273328552369 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200336041173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_56 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (82153055349187 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200340078689 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨56, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (82153055349187 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200340078689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_57 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (2052987633823 / 2500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100172022301 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨57, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (2052987633823 / 2500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100172022301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_58 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41042989201399 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200348112101 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨58, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41042989201399 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200348112101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_59 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (82052474471607 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200352099041 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨59, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (82052474471607 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200352099041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13142_40 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (20673249606671 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200164585291 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨40, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (20673249606671 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200164585291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_41 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (8265907588359 / 10000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100084299917 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨41, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (8265907588359 / 10000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100084299917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_42 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82625176841103 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137510790167 / 6250000000000 : ℝ))
      (E := (cell13142 ⟨42, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82625176841103 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137510790167 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_43 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (16518260253947 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (110008832687 / 5000000000000 : ℝ))
      (E := (cell13142 ⟨43, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (16518260253947 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (110008832687 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_44 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82557449140149 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (275022586303 / 12500000000000 : ℝ))
      (E := (cell13142 ⟨44, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82557449140149 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (275022586303 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_45 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (16504724084631 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (88007387687 / 4000000000000 : ℝ))
      (E := (cell13142 ⟨45, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (16504724084631 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (88007387687 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_46 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (41244907544853 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (550047179 / 25000000000 : ℝ))
      (E := (cell13142 ⟨46, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (41244907544853 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (550047179 / 25000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_47 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82456033110907 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200192700871 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨47, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82456033110907 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200192700871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_48 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82422274458001 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (220019676239 / 10000000000000 : ℝ))
      (E := (cell13142 ⟨48, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82422274458001 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (220019676239 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_49 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82388539102381 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200200780129 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨49, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82388539102381 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200200780129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_50 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (41177413507789 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200204751309 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨50, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (41177413507789 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200204751309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_51 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (8232113816927 / 10000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200208791033 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨51, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (8232113816927 / 10000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200208791033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_52 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82287472535273 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (550053209293 / 25000000000000 : ℝ))
      (E := (cell13142 ⟨52, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82287472535273 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (550053209293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_53 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (41126915042773 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200216827289 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨53, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (41126915042773 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200216827289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_54 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (16444042158437 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (550055219001 / 25000000000000 : ℝ))
      (E := (cell13142 ⟨54, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (16444042158437 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (550055219001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_55 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (20546653656857 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440044972269 / 20000000000000 : ℝ))
      (E := (cell13142 ⟨55, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (20546653656857 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440044972269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_56 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82153041563651 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200228897607 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨56, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82153041563651 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200228897607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_57 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (16423898314673 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100116460751 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨57, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (16423898314673 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100116460751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_58 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82085964629221 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (550059232163 / 25000000000000 : ℝ))
      (E := (cell13142 ⟨58, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82085964629221 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (550059232163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_59 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82052460704003 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (220024097371 / 10000000000000 : ℝ))
      (E := (cell13142 ⟨59, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82052460704003 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (220024097371 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13143_40 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (5168311534181 / 6250000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200053484373 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨40, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (5168311534181 / 6250000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200053484373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_41 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82659062009861 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (440011499399 / 20000000000000 : ℝ))
      (E := (cell13143 ⟨41, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82659062009861 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (440011499399 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_42 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82625162973427 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (17600491833 / 800000000000 : ℝ))
      (E := (cell13143 ⟨42, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82625162973427 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (17600491833 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_43 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (20647821852027 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100032744171 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨43, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (20647821852027 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100032744171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_44 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41278717642283 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200069523221 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨44, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41278717642283 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200069523221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_45 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (8252360657361 / 10000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (440014704643 / 20000000000000 : ℝ))
      (E := (cell13143 ⟨45, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (8252360657361 / 10000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (440014704643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_46 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (20622450311549 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100038772663 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨46, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (20622450311549 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100038772663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_47 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (3298240770937 / 4000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100040793743 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨47, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (3298240770937 / 4000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100040793743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_48 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (5151391289159 / 6250000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200085588431 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨48, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (5151391289159 / 6250000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200085588431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_49 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82388525276943 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (440017920919 / 20000000000000 : ℝ))
      (E := (cell13143 ⟨49, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82388525276943 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (440017920919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_50 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (20588703299039 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (220009363327 / 10000000000000 : ℝ))
      (E := (cell13143 ⟨50, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (20588703299039 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (220009363327 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_51 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82321124355857 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (137506104471 / 6250000000000 : ℝ))
      (E := (cell13143 ⟨51, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82321124355857 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (137506104471 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_52 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (16457491745573 / 20000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200101657191 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨52, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (16457491745573 / 20000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200101657191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_53 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41126908142069 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200105705013 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨53, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41126908142069 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200105705013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_54 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82220196996773 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200109693289 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨54, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82220196996773 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200109693289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_55 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82186600838007 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (275014217059 / 12500000000000 : ℝ))
      (E := (cell13143 ⟨55, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82186600838007 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (275014217059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_56 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (16430605556043 / 20000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100058885753 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨56, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (16430605556043 / 20000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100058885753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_57 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82119477795911 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200121735029 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨57, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82119477795911 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200121735029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_58 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82085950857743 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (220012580023 / 10000000000000 : ℝ))
      (E := (cell13143 ⟨58, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82085950857743 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (220012580023 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_59 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (641034741707 / 781250000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200129784963 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨59, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (641034741707 / 781250000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200129784963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13144_40 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41346485334611 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549985580117 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨40, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41346485334611 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549985580117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_41 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (20664762034561 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (43998926623 / 2000000000000 : ℝ))
      (E := (cell13144 ⟨41, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (20664762034561 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (43998926623 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_42 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82625149107863 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199950370219 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨42, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82625149107863 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199950370219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_43 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82591273548593 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199954377609 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨43, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82591273548593 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199954377609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_44 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41278710715547 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549989602677 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨44, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41278710715547 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549989602677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_45 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (2578862272693 / 3125000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199962408967 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨45, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (2578862272693 / 3125000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199962408967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_46 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (16497957480959 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199966429391 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨46, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (16497957480959 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199966429391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_47 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (20614001359513 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549992617477 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨47, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (20614001359513 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549992617477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_48 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (16484449359439 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199974469257 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨48, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (16484449359439 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199974469257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_49 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (20597127863403 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (68749327621 / 3125000000000 : ℝ))
      (E := (cell13144 ⟨49, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (20597127863403 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (68749327621 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_50 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41177399689419 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199982511043 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨50, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41177399689419 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199982511043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_51 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82321110544549 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (43999730957 / 2000000000000 : ℝ))
      (E := (cell13144 ⟨51, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82321110544549 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (43999730957 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_52 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82287444922561 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099995266047 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨52, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82287444922561 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099995266047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_53 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82253802484833 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (43999891571 / 2000000000000 : ℝ))
      (E := (cell13144 ⟨53, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82253802484833 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (43999891571 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_54 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41110091601731 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099999282753 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨54, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41110091601731 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099999282753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_55 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41093293525343 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (275000325927 / 12500000000000 : ℝ))
      (E := (cell13144 ⟨55, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41093293525343 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (275000325927 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_56 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82153013998879 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2200006641221 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨56, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82153013998879 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2200006641221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_57 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (16423892804111 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2200010662751 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨57, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (16423892804111 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2200010662751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_58 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41042968544181 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (550003666907 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨58, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41042968544181 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (550003666907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_59 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82052433175087 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2200018651269 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨59, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82052433175087 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2200018651269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13145_40 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41346478396831 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199831211157 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨40, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41346478396831 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199831211157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_41 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82659034268741 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199835278733 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨41, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82659034268741 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199835278733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_42 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (20656283811103 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099919628559 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨42, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (20656283811103 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099919628559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_43 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82591259691189 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099921631341 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨43, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82591259691189 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099921631341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_44 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (20639351894933 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099923647001 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨44, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (20639351894933 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099923647001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_45 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82523578880851 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (68745352829 / 3125000000000 : ℝ))
      (E := (cell13145 ⟨45, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82523578880851 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (68745352829 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_46 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41244886782751 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (137490956829 / 6250000000000 : ℝ))
      (E := (cell13145 ⟨46, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41244886782751 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (137490956829 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_47 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82455991604787 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (109992967407 / 5000000000000 : ℝ))
      (E := (cell13145 ⟨47, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82455991604787 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (109992967407 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_48 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (2575694780311 / 3125000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099931672947 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨48, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (2575694780311 / 3125000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099931672947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_49 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82388497632387 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (54996685449 / 2500000000000 : ℝ))
      (E := (cell13145 ⟨49, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82388497632387 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (54996685449 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_50 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41177392781813 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (549967846157 / 25000000000000 : ℝ))
      (E := (cell13145 ⟨50, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41177392781813 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (549967846157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_51 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (5145068545959 / 6250000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199875419979 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨51, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (5145068545959 / 6250000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199875419979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_52 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82287431119359 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099939730941 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨52, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82287431119359 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099939730941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_53 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (8225378868763 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099941723951 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨53, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (8225378868763 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099941723951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_54 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (20555042353063 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199887492657 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨54, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (20555042353063 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199887492657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_55 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (16437314653093 / 20000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (8593326071 / 390625000000 : ℝ))
      (E := (cell13145 ⟨55, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (16437314653093 / 20000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (8593326071 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_56 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41076500109821 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (439979101351 / 20000000000000 : ℝ))
      (E := (cell13145 ⟨56, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41076500109821 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (439979101351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_57 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41059725123649 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099949763551 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨57, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41059725123649 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099949763551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_58 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (2052148083027 / 2500000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199903530843 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨58, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (2052148083027 / 2500000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199903530843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_59 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41026209706887 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199907572631 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨59, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41026209706887 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199907572631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13146_40 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (10336617865027 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199720156439 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨40, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (10336617865027 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199720156439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_41 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82659020401351 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549931040827 / 25000000000000 : ℝ))
      (E := (cell13146 ⟨41, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82659020401351 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549931040827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_42 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82625121383073 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199728198659 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨42, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82625121383073 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199728198659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_43 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (16518249167179 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199732202423 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨43, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (16518249167179 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199732202423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_44 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82557393730479 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199736231987 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨44, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82557393730479 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199736231987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_45 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (16504713007527 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199740226803 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨45, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (16504713007527 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199740226803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_46 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82489759728317 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199744243877 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨46, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82489759728317 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199744243877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_47 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82455977773629 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439949656227 / 20000000000000 : ℝ))
      (E := (cell13146 ⟨47, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82455977773629 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439949656227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_48 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (16484443828963 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199752277319 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨48, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (16484443828963 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199752277319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_49 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82388483813267 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (109987814443 / 5000000000000 : ℝ))
      (E := (cell13146 ⟨49, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82388483813267 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (109987814443 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_50 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41177385875259 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199760313049 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨50, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41177385875259 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199760313049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_51 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82321082928243 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (274970543371 / 12500000000000 : ℝ))
      (E := (cell13146 ⟨51, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82321082928243 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (274970543371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_52 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82287417318261 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199768387483 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨52, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82287417318261 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199768387483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_53 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (5140860930783 / 6250000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549943093041 / 25000000000000 : ℝ))
      (E := (cell13146 ⟨53, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (5140860930783 / 6250000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549943093041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_54 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (10277519452893 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199776415623 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨54, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (10277519452893 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199776415623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_55 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (10273319935293 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099890197947 / 50000000000000 : ℝ))
      (E := (cell13146 ⟨55, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (10273319935293 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099890197947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_56 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (16430597288501 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199784427269 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨56, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (16430597288501 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199784427269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_57 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41059718238069 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199788446461 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨57, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41059718238069 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199788446461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_58 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41042954777947 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199792449091 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨58, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41042954777947 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199792449091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_59 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41026202827279 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199796489813 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨59, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41026202827279 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199796489813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13147_40 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82692929048883 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099804548763 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨40, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82692929048883 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099804548763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_41 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82659006536073 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274951637813 / 12500000000000 : ℝ))
      (E := (cell13147 ⟨41, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82659006536073 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274951637813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_42 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16525021504769 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274952142001 / 12500000000000 : ℝ))
      (E := (cell13147 ⟨42, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16525021504769 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274952142001 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_43 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (10323903997839 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199621137971 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨43, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (10323903997839 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199621137971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_44 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82557379883337 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (109981258289 / 5000000000000 : ℝ))
      (E := (cell13147 ⟨44, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82557379883337 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (109981258289 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_45 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (5157721949783 / 6250000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199629158889 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨45, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (5157721949783 / 6250000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199629158889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_46 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82489745893241 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (21996331743 / 1000000000000 : ℝ))
      (E := (cell13147 ⟨46, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82489745893241 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (21996331743 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_47 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82455963944577 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274954651243 / 12500000000000 : ℝ))
      (E := (cell13147 ⟨47, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82455963944577 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274954651243 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_48 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (10302775665223 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199641204557 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨48, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (10302775665223 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199641204557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_49 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (20597117499063 / 25000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099822636787 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨49, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (20597117499063 / 25000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099822636787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_50 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41177378969757 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (439929847457 / 20000000000000 : ℝ))
      (E := (cell13147 ⟨50, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41177378969757 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (439929847457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_51 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16464213824649 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549913317443 / 25000000000000 : ℝ))
      (E := (cell13147 ⟨51, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16464213824649 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549913317443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_52 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (2571481359977 / 3125000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099828654451 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨52, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (2571481359977 / 3125000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099828654451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_53 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (10281720137441 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099830646121 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨53, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (10281720137441 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099830646121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_54 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16444028367227 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274958166801 / 12500000000000 : ℝ))
      (E := (cell13147 ⟨54, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16444028367227 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274958166801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_55 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82186545701323 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199669372571 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨55, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82186545701323 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199669372571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_56 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41076486333733 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (137479587673 / 6250000000000 : ℝ))
      (E := (cell13147 ⟨56, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41076486333733 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (137479587673 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_57 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82119422707077 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199677420827 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨57, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82119422707077 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199677420827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_58 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41042947896403 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (219968142237 / 10000000000000 : ℝ))
      (E := (cell13147 ⟨58, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41042947896403 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (219968142237 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_59 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82052391897437 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549921365513 / 25000000000000 : ℝ))
      (E := (cell13147 ⟨59, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82052391897437 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549921365513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13148_40 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41346457589831 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199498034421 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨40, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41346457589831 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199498034421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_41 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82658992672907 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439900407501 / 20000000000000 : ℝ))
      (E := (cell13148 ⟨41, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82658992672907 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439900407501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_42 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (10328136708341 / 12500000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549876517291 / 25000000000000 : ℝ))
      (E := (cell13148 ⟨42, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (10328136708341 / 12500000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549876517291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_43 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (2064780453291 / 2500000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199510069327 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨43, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (2064780453291 / 2500000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199510069327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_44 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82557366038303 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (274939261923 / 12500000000000 : ℝ))
      (E := (cell13148 ⟨44, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82557366038303 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (274939261923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_45 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (10315442169691 / 12500000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549879536423 / 25000000000000 : ℝ))
      (E := (cell13148 ⟨45, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (10315442169691 / 12500000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549879536423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_46 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82489732060271 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439904431893 / 20000000000000 : ℝ))
      (E := (cell13148 ⟨46, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82489732060271 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439904431893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_47 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (322093555147 / 390625000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199526193517 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨47, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (322093555147 / 390625000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199526193517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_48 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82422191500859 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (274941273323 / 12500000000000 : ℝ))
      (E := (cell13148 ⟨48, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82422191500859 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (274941273323 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_49 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82388456181341 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099767097551 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨49, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82388456181341 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099767097551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_50 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82354744130613 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (54988455409 / 2500000000000 : ℝ))
      (E := (cell13148 ⟨50, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82354744130613 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (54988455409 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_51 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (1646421106407 / 2000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099771123719 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨51, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (1646421106407 / 2000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099771123719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_52 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82287389722369 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (274943285651 / 12500000000000 : ℝ))
      (E := (cell13148 ⟨52, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82287389722369 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (274943285651 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_53 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82253747308629 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199550267231 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨53, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82253747308629 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199550267231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_54 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82220128051227 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (68736072129 / 3125000000000 : ℝ))
      (E := (cell13148 ⟨54, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82220128051227 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (68736072129 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_55 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (102733164903 / 125000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199558345069 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨55, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (102733164903 / 125000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199558345069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_56 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (3286118355781 / 4000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099781157461 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨56, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (3286118355781 / 4000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099781157461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_57 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (5132463058757 / 6250000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099783165913 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨57, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (5132463058757 / 6250000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099783165913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_58 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82085882031813 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (137473149467 / 6250000000000 : ℝ))
      (E := (cell13148 ⟨58, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82085882031813 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (137473149467 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_59 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (20513094535603 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099787185439 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨59, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (20513094535603 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099787185439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13149_40 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41346450656277 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (274923378239 / 12500000000000 : ℝ))
      (E := (cell13149 ⟨40, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41346450656277 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (274923378239 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_41 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20664744702963 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199391027129 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨41, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20664744702963 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199391027129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_42 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (82625079811721 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199395056967 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨42, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (82625079811721 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199395056967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_43 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20647801070669 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439879811071 / 20000000000000 : ℝ))
      (E := (cell13149 ⟨43, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20647801070669 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439879811071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_44 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41278676097689 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099701539841 / 50000000000000 : ℝ))
      (E := (cell13149 ⟨44, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41278676097689 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099701539841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_45 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (82523523520637 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199407128307 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨45, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (82523523520637 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199407128307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_46 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (2577803694669 / 3125000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199411140443 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨46, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (2577803694669 / 3125000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199411140443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_47 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (82455936292793 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (274926896613 / 12500000000000 : ℝ))
      (E := (cell13149 ⟨47, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (82455936292793 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (274926896613 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_48 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41211088841019 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199419164427 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨48, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41211088841019 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199419164427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_49 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (16477688473707 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439884634289 / 20000000000000 : ℝ))
      (E := (cell13149 ⟨49, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (16477688473707 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439884634289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_50 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (16470946064763 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199427191251 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨50, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (16470946064763 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199427191251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_51 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20580260379889 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549857805231 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨51, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20580260379889 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549857805231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_52 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (3291495037103 / 4000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549858814333 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨52, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (3291495037103 / 4000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549858814333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_53 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (8225373351983 / 10000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199439238041 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨53, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (8225373351983 / 10000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199439238041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_54 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41110057134209 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549860819417 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨54, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41110057134209 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549860819417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_55 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (10273314768197 / 12500000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099723656693 / 50000000000000 : ℝ))
      (E := (cell13149 ⟨55, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (10273314768197 / 12500000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099723656693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_56 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (82152945123681 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549862835307 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨56, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (82152945123681 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549862835307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_57 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (16423879035049 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (68732979907 / 3125000000000 : ℝ))
      (E := (cell13149 ⟨57, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (16423879035049 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (68732979907 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_58 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20521467068229 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199459356397 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨58, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20521467068229 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199459356397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_59 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (82052364389481 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099731697 / 50000000000 : ℝ))
      (E := (cell13149 ⟨59, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (82052364389481 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099731697 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

end BstLean.Part268
