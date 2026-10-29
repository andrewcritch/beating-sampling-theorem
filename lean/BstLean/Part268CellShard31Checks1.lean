import BstLean.Part268CellShard31Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13125_20 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83376669537999 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1100988463363 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨20, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83376669537999 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1100988463363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_21 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83342270449303 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (220198091981 / 10000000000000 : ℝ))
      (E := (cell13125 ⟨21, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83342270449303 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (220198091981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_22 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83307895483589 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201984918031 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨22, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83307895483589 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201984918031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_23 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83273544608207 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201988924703 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨23, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83273544608207 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201988924703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_24 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41619608895339 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201992942903 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨24, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41619608895339 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201992942903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_25 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83204914998687 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201996975473 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨25, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83204914998687 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201996975473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_26 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (16634127240017 / 20000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202000966567 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨26, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (16634127240017 / 20000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202000966567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_27 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41568190681443 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202004976977 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨27, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41568190681443 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202004976977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_28 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83102150455271 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (137625563053 / 6250000000000 : ℝ))
      (E := (cell13125 ⟨28, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83102150455271 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (137625563053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_29 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (4153397172279 / 5000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202013005569 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨29, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (4153397172279 / 5000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202013005569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_30 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (20758440075579 / 25000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (137626064207 / 6250000000000 : ℝ))
      (E := (cell13125 ⟨30, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (20758440075579 / 25000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (137626064207 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_31 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82999600994141 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101010537769 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨31, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82999600994141 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101010537769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_32 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41482732744939 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202025092879 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨32, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41482732744939 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202025092879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_33 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41465676879253 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101014540137 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨33, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41465676879253 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101014540137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_34 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41448632884583 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550508274269 / 25000000000000 : ℝ))
      (E := (cell13125 ⟨34, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41448632884583 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550508274269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_35 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (1657264029823 / 2000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202037143847 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨35, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (1657264029823 / 2000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202037143847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_36 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82829160893909 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202041162223 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨36, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82829160893909 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202041162223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_37 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (10349392993381 / 12500000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101022576123 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨37, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (10349392993381 / 12500000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101022576123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_38 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41380575310163 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101024586237 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨38, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41380575310163 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1101024586237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_39 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (82727180883653 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202053163811 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨39, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (82727180883653 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2202053163811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13126_20 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (8337665549963 / 10000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (44037308417 / 2000000000000 : ℝ))
      (E := (cell13126 ⟨20, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (8337665549963 / 10000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (44037308417 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_21 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83342256417111 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100934705431 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨21, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83342256417111 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100934705431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_22 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83307881457569 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201873464423 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨22, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83307881457569 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201873464423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_23 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41636765294177 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (110093873407 / 5000000000000 : ℝ))
      (E := (cell13126 ⟨23, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41636765294177 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (110093873407 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_24 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41619601888493 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220188148343 / 10000000000000 : ℝ))
      (E := (cell13126 ⟨24, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41619601888493 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220188148343 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_25 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83204900991151 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100942727351 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨25, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83204900991151 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100942727351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_26 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (831706221987 / 1000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275236187677 / 12500000000000 : ℝ))
      (E := (cell13126 ⟨26, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (831706221987 / 1000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275236187677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_27 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (2598011480239 / 3125000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440378701811 / 20000000000000 : ℝ))
      (E := (cell13126 ⟨27, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (2598011480239 / 3125000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440378701811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_28 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83102136466173 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201897538203 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨28, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83102136466173 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201897538203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_29 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41533964731309 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201901532247 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨29, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41533964731309 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201901532247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_30 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (20758436581371 / 25000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201905551359 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨30, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (20758436581371 / 25000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201905551359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_31 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41499793511717 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (88076381537 / 4000000000000 : ℝ))
      (E := (cell13126 ⟨31, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41499793511717 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (88076381537 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_32 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (8296545152529 / 10000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440382710641 / 20000000000000 : ℝ))
      (E := (cell13126 ⟨32, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (8296545152529 / 10000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440382710641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_33 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41465669900017 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201917596707 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨33, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41465669900017 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201917596707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_34 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82897251816803 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440384322213 / 20000000000000 : ℝ))
      (E := (cell13126 ⟨34, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82897251816803 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440384322213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_35 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (20715796886223 / 25000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550481413859 / 25000000000000 : ℝ))
      (E := (cell13126 ⟨35, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (20715796886223 / 25000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550481413859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_36 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (66263317563 / 80000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201929612767 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨36, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (66263317563 / 80000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201929612767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_37 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (10349391251623 / 12500000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275241707397 / 12500000000000 : ℝ))
      (E := (cell13126 ⟨37, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (10349391251623 / 12500000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275241707397 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_38 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82761136692351 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275242209643 / 12500000000000 : ℝ))
      (E := (cell13126 ⟨38, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82761136692351 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275242209643 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_39 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (82727166961763 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100970833133 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨39, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (82727166961763 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100970833133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13127_20 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41688320731701 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100876955371 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨20, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41688320731701 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100876955371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_21 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (4167112119353 / 5000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (88070318241 / 4000000000000 : ℝ))
      (E := (cell13127 ⟨21, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (4167112119353 / 5000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (88070318241 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_22 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (10413483429211 / 12500000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (110088097411 / 5000000000000 : ℝ))
      (E := (cell13127 ⟨22, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (10413483429211 / 12500000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (110088097411 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_23 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (1040918957133 / 1250000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100883003673 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨23, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (1040918957133 / 1250000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100883003673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_24 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83239189765433 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201770019727 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨24, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83239189765433 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201770019727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_25 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83204886985753 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100886994069 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨25, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83204886985753 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100886994069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_26 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (20792652049863 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (550444508009 / 25000000000000 : ℝ))
      (E := (cell13127 ⟨26, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (20792652049863 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (550444508009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_27 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (5196022085909 / 6250000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201782036907 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨27, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (5196022085909 / 6250000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201782036907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_28 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83102122479209 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (550446515833 / 25000000000000 : ℝ))
      (E := (cell13127 ⟨28, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83102122479209 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (550446515833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_29 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (20766978870447 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201790054701 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨29, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (20766978870447 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201790054701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_30 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83033732350783 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (137612129449 / 6250000000000 : ℝ))
      (E := (cell13127 ⟨30, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83033732350783 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (137612129449 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_31 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41499786527429 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201798114241 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨31, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41499786527429 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201798114241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_32 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82965437562833 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (550450531627 / 25000000000000 : ℝ))
      (E := (cell13127 ⟨32, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82965437562833 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (550450531627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_33 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82931325843691 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201806108919 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨33, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82931325843691 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201806108919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_34 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (10362154733321 / 12500000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201810120833 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨34, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (10362154733321 / 12500000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201810120833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_35 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82863173600761 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100907081403 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨35, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82863173600761 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100907081403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_36 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41414566507859 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100909088239 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨36, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41414566507859 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100909088239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_37 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41397558040523 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (68806942559 / 3125000000000 : ℝ))
      (E := (cell13127 ⟨37, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41397558040523 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (68806942559 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_38 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (82761122766501 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201826177597 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨38, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (82761122766501 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201826177597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_39 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (20681788260499 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201830223271 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨39, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (20681788260499 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201830223271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13128_20 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (16675325485863 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (27520531413 / 1250000000000 : ℝ))
      (E := (cell13128 ⟨20, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (16675325485863 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (27520531413 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_21 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (20835557089787 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201646496957 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨21, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (20835557089787 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201646496957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_22 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83307853411947 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201650486151 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨22, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83307853411947 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201650486151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_23 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83273502555063 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550413635581 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨23, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83273502555063 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550413635581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_24 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (5202448484751 / 6250000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100829275899 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨24, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (5202448484751 / 6250000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100829275899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_25 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83204872982491 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201662575783 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨25, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83204872982491 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201662575783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_26 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (41585297101169 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (68802079951 / 3125000000000 : ℝ))
      (E := (cell13128 ⟨26, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (41585297101169 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (68802079951 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_27 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (3325453575343 / 4000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201670560533 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨27, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (3325453575343 / 4000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201670560533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_28 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83102108494379 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550418646059 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨28, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83102108494379 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550418646059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_29 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83067901503091 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (110083931573 / 5000000000000 : ℝ))
      (E := (cell13128 ⟨29, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83067901503091 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (110083931573 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_30 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (16606743675643 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201682645337 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨30, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (16606743675643 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201682645337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_31 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (20749889772103 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (110084331363 / 5000000000000 : ℝ))
      (E := (cell13128 ⟨31, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (20749889772103 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (110084331363 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_32 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (41482711801253 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (220169063699 / 10000000000000 : ℝ))
      (E := (cell13128 ⟨32, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (41482711801253 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (220169063699 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_33 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (20732827972369 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (440338935107 / 20000000000000 : ℝ))
      (E := (cell13128 ⟨33, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (20732827972369 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (440338935107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_34 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (41448611959231 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550424671257 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨34, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (41448611959231 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550424671257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_35 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (82863159658757 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550425681157 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨35, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (82863159658757 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550425681157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_36 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (20707279769953 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550426683993 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨36, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (20707279769953 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550426683993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_37 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (1293673471113 / 1562500000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201710719101 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨37, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (1293673471113 / 1562500000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201710719101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_38 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (3310444353711 / 4000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (88068589303 / 4000000000000 : ℝ))
      (E := (cell13128 ⟨38, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (3310444353711 / 4000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (88068589303 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_39 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (82727139124353 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201718776059 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨39, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (82727139124353 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201718776059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13129_20 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (10422076674671 / 12500000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (275191381599 / 12500000000000 : ℝ))
      (E := (cell13129 ⟨20, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (10422076674671 / 12500000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (275191381599 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_21 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (1302222098959 / 1562500000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (440307018401 / 20000000000000 : ℝ))
      (E := (cell13129 ⟨21, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (1302222098959 / 1562500000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (440307018401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_22 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (16661567878469 / 20000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201539078221 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨22, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (16661567878469 / 20000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201539078221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_23 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (666187908333 / 800000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (88061722923 / 4000000000000 : ℝ))
      (E := (cell13129 ⟨23, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (666187908333 / 800000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (88061722923 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_24 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (325152975581 / 390625000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201547079643 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨24, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (325152975581 / 390625000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201547079643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_25 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (20801214745341 / 25000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201551100769 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨25, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (20801214745341 / 25000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201551100769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_26 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (64977015787 / 78125000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100777569531 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨26, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (64977015787 / 78125000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100777569531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_27 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (4156816269737 / 5000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (110077956921 / 5000000000000 : ℝ))
      (E := (cell13129 ⟨27, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (4156816269737 / 5000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (110077956921 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_28 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83102094511681 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201563159427 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨28, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83102094511681 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201563159427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_29 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (41533943763263 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201567203999 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨29, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (41533943763263 / 50000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201567203999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_30 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83033704407777 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (275196401909 / 12500000000000 : ℝ))
      (E := (cell13129 ⟨30, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83033704407777 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (275196401909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_31 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82999545124097 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550393798659 / 25000000000000 : ℝ))
      (E := (cell13129 ⟨31, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82999545124097 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550393798659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_32 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (20741352411077 / 25000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100789600927 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨32, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (20741352411077 / 25000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100789600927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_33 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (8293129793739 / 10000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100791618967 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨33, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (8293129793739 / 10000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100791618967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_34 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82897209972483 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201587245007 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨34, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82897209972483 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201587245007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_35 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (517894660743 / 625000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100795641117 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨35, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (517894660743 / 625000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100795641117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_36 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (5176819071627 / 6250000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201595291251 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨36, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (5176819071627 / 6250000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201595291251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_37 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82795088223543 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201599272101 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨37, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82795088223543 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201599272101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_38 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (82761094921173 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1720002611 / 78125000000 : ℝ))
      (E := (cell13129 ⟨38, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (82761094921173 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1720002611 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_39 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (323152832847 / 390625000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201607324637 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨39, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (323152832847 / 390625000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201607324637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13130_20 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41688299683781 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201419646631 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨20, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41688299683781 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201419646631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_21 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (5208887519359 / 6250000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201423624479 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨21, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (5208887519359 / 6250000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201423624479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_22 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (520673908593 / 625000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137589229129 / 6250000000000 : ℝ))
      (E := (cell13130 ⟨22, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (520673908593 / 625000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137589229129 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_23 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83273474530323 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201431657989 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨23, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83273474530323 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201431657989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_24 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (10404893467949 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201435720087 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨24, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (10404893467949 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201435720087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_25 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83204844982373 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201439679963 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨25, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83204844982373 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201439679963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_26 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (20792641553629 / 25000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (550360928867 / 25000000000000 : ℝ))
      (E := (cell13130 ⟨26, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (20792641553629 / 25000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (550360928867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_27 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41568155704019 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201447712083 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨27, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41568155704019 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201447712083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_28 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (20775520132779 / 25000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201451730393 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨28, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (20775520132779 / 25000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201451730393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_29 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83067873552093 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440291154463 / 20000000000000 : ℝ))
      (E := (cell13130 ⟨29, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83067873552093 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440291154463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_30 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (8303369043947 / 10000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (275182472623 / 12500000000000 : ℝ))
      (E := (cell13130 ⟨30, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (8303369043947 / 10000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (275182472623 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_31 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (10374941395239 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201463816367 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨31, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (10374941395239 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201463816367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_32 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41482697844119 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201467821099 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨32, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41482697844119 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201467821099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_33 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (10366410498429 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137591987257 / 6250000000000 : ℝ))
      (E := (cell13130 ⟨33, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (10366410498429 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137591987257 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_34 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82897196028631 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440295171883 / 20000000000000 : ℝ))
      (E := (cell13130 ⟨34, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82897196028631 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440295171883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_35 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82863131781129 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100739917811 / 50000000000000 : ℝ))
      (E := (cell13130 ⟨35, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82863131781129 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100739917811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_36 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (10353636401797 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440296768463 / 20000000000000 : ℝ))
      (E := (cell13130 ⟨36, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (10353636401797 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440296768463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_37 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (82795074297979 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201487879601 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨37, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (82795074297979 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201487879601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_38 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41380540500847 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (220149188863 / 10000000000000 : ℝ))
      (E := (cell13130 ⟨38, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41380540500847 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (220149188863 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_39 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41363555647717 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201495927763 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨39, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41363555647717 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201495927763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13131_20 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (16675317067979 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201308236243 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨20, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (16675317067979 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201308236243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_21 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (333368745153 / 400000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201312269413 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨21, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (333368745153 / 400000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201312269413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_22 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83307811359553 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201316249681 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨22, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83307811359553 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201316249681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_23 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83273460521159 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100660148533 / 50000000000000 : ℝ))
      (E := (cell13131 ⟨23, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83273460521159 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100660148533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_24 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (16647826748117 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100662148947 / 50000000000000 : ℝ))
      (E := (cell13131 ⟨24, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (16647826748117 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100662148947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_25 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83204830985517 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550332078343 / 25000000000000 : ℝ))
      (E := (cell13131 ⟨25, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83204830985517 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550332078343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_26 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41585276111903 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (8598954477 / 390625000000 : ℝ))
      (E := (cell13131 ⟨26, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41585276111903 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (8598954477 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_27 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83136297423469 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (275167042501 / 12500000000000 : ℝ))
      (E := (cell13131 ⟨27, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83136297423469 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (275167042501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_28 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (20775516638171 / 25000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440268071129 / 20000000000000 : ℝ))
      (E := (cell13131 ⟨28, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (20775516638171 / 25000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440268071129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_29 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83067859579791 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201344394941 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨29, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83067859579791 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201344394941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_30 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41516838236647 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201348401031 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨30, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41516838236647 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201348401031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_31 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (16599903440371 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440270475061 / 20000000000000 : ℝ))
      (E := (cell13131 ⟨31, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (16599903440371 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440270475061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_32 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41482690867149 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (17610851489 / 800000000000 : ℝ))
      (E := (cell13131 ⟨32, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41482690867149 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (17610851489 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_33 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (82931270039601 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (22013604087 / 1000000000000 : ℝ))
      (E := (cell13131 ⟨33, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (82931270039601 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (22013604087 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_34 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (16579436417381 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (275170558701 / 12500000000000 : ℝ))
      (E := (cell13131 ⟨34, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (16579436417381 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (275170558701 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_35 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (82863117845503 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201368443467 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨35, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (82863117845503 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201368443467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_36 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41414538642423 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201372506551 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨36, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41414538642423 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201372506551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_37 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41397530187269 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201376482889 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨37, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41397530187269 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201376482889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_38 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41380533542169 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201380489709 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨38, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41380533542169 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201380489709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_39 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41363548692079 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201384526679 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨39, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41363548692079 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201384526679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13132_20 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (1302758926787 / 1562500000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550299219987 / 25000000000000 : ℝ))
      (E := (cell13132 ⟨20, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (1302758926787 / 1562500000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550299219987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_21 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (41671086134447 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201200910121 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨21, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (41671086134447 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201200910121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_22 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (20826949336591 / 25000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100602443719 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨22, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (20826949336591 / 25000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100602443719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_23 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (8327344651413 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100604465961 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨23, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (8327344651413 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100604465961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_24 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (1300611245933 / 1562500000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201212929891 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨24, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (1300611245933 / 1562500000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201212929891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_25 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16640963398159 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100608471279 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨25, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16640963398159 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100608471279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_26 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (8317053823523 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100610486267 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨26, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (8317053823523 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100610486267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_27 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (83136283441033 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (17197070029 / 781250000000 : ℝ))
      (E := (cell13132 ⟨27, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (83136283441033 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (17197070029 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_28 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (41551026288191 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100614488339 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨28, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (41551026288191 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100614488339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_29 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (83067845609619 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (44024660267 / 2000000000000 : ℝ))
      (E := (cell13132 ⟨29, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (83067845609619 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (44024660267 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_30 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (83033662509247 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201237016861 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨30, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (83033662509247 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201237016861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_31 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (10374937905491 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201241047179 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨31, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (10374937905491 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201241047179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_32 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16593073556497 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201245046937 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨32, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16593073556497 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201245046937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_33 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (41465628046949 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440249815139 / 20000000000000 : ℝ))
      (E := (cell13132 ⟨33, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (41465628046949 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440249815139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_34 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16579433629461 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201253075587 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨34, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16579433629461 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201253075587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_35 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (41431551956001 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (220125710577 / 10000000000000 : ℝ))
      (E := (cell13132 ⟨35, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (41431551956001 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (220125710577 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_36 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82829063357439 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201261107883 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨36, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82829063357439 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201261107883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_37 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (4139752322661 / 5000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201265140683 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨37, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (4139752322661 / 5000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201265140683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_38 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (5172565823069 / 6250000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201269145319 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨38, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (5172565823069 / 6250000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201269145319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_39 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (82727083475003 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (44025463603 / 2000000000000 : ℝ))
      (E := (cell13132 ⟨39, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (82727083475003 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (44025463603 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13133_20 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83376557290979 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201085519427 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨20, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83376557290979 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201085519427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_21 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (3333686330067 / 4000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440217909321 / 20000000000000 : ℝ))
      (E := (cell13133 ⟨21, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (3333686330067 / 4000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440217909321 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_22 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83307783335311 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201093579339 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨22, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83307783335311 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201093579339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_23 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41636716254619 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275137195319 / 12500000000000 : ℝ))
      (E := (cell13133 ⟨23, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41636716254619 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275137195319 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_24 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (3329564229639 / 4000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440220311533 / 20000000000000 : ℝ))
      (E := (cell13133 ⟨24, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (3329564229639 / 4000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440220311533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_25 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83204802998207 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201105567523 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨25, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83204802998207 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201105567523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_26 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83170524248787 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100554797367 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨26, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83170524248787 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100554797367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_27 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83136269460729 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201113641679 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨27, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83136269460729 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201113641679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_28 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (20775509650553 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201117651999 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨28, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (20775509650553 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201117651999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_29 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41533915820789 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201121627539 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨29, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41533915820789 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201121627539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_30 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83033648547329 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201125687027 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨30, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83033648547329 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201125687027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_31 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82999489288129 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201129656259 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨31, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82999489288129 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201129656259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_32 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82965353832799 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201133712133 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨32, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82965353832799 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201133712133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_33 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (1036640526879 / 1250000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550284434619 / 25000000000000 : ℝ))
      (E := (cell13133 ⟨33, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (1036640526879 / 1250000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550284434619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_34 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82897154209831 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201141735999 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨34, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82897154209831 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201141735999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_35 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41431544990313 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (110057288193 / 5000000000000 : ℝ))
      (E := (cell13133 ⟨35, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41431544990313 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (110057288193 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_36 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (20707262358039 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (137571860231 / 6250000000000 : ℝ))
      (E := (cell13133 ⟨36, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (20707262358039 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (137571860231 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_37 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (3311801301361 / 4000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100576897133 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨37, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (3311801301361 / 4000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100576897133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_38 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (10345129906999 / 12500000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201157796717 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨38, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (10345129906999 / 12500000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201157796717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_39 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (82727069567969 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201161829411 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨39, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (82727069567969 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201161829411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13134_20 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (2605516977179 / 3125000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200974213 / 100000000000 : ℝ))
      (E := (cell13134 ⟨20, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (2605516977179 / 3125000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200974213 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_21 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41671072118297 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200978237207 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨21, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41671072118297 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200978237207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_22 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (16661553865279 / 20000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275122776081 / 12500000000000 : ℝ))
      (E := (cell13134 ⟨22, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (16661553865279 / 20000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275122776081 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_23 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83273418506481 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (44019724947 / 2000000000000 : ℝ))
      (E := (cell13134 ⟨23, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83273418506481 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (44019724947 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_24 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83239091744371 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (137561889977 / 6250000000000 : ℝ))
      (E := (cell13134 ⟨24, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83239091744371 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (137561889977 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_25 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83204789007753 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200994246703 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨25, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83204789007753 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200994246703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_26 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (20792627566119 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275124783897 / 12500000000000 : ℝ))
      (E := (cell13134 ⟨26, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (20792627566119 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275124783897 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_27 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (20784063870639 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (550250578857 / 25000000000000 : ℝ))
      (E := (cell13134 ⟨27, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (20784063870639 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (550250578857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_28 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83102024630173 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201006323101 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨28, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83102024630173 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201006323101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_29 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83067817675667 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201010296041 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨29, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83067817675667 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201010296041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_30 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83033634587541 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (88040574119 / 4000000000000 : ℝ))
      (E := (cell13134 ⟨30, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83033634587541 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (88040574119 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_31 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41499737667229 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100509189139 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨31, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41499737667229 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100509189139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_32 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (2074133497131 / 2500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (440204474623 / 20000000000000 : ℝ))
      (E := (cell13134 ⟨32, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (2074133497131 / 2500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (440204474623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_33 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (82931228208869 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201026397043 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨33, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (82931228208869 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201026397043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_34 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41448570137241 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100515196099 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨34, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41448570137241 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100515196099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_35 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41431538025687 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201034417737 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨35, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41431538025687 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201034417737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_36 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (20707258877249 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201038415297 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨36, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (20707258877249 / 25000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201038415297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_37 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10349377327119 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100521221819 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨37, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10349377327119 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100521221819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_38 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (82761025345001 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201046443907 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨38, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (82761025345001 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201046443907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_39 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (16545411132611 / 20000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201050474463 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨39, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (16545411132611 / 20000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2201050474463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13135_20 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41688264625307 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200862902351 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨20, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41688264625307 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200862902351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_21 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (1666842604473 / 2000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100433461793 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨21, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (1666842604473 / 2000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100433461793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_22 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41653877659807 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275108861513 / 12500000000000 : ℝ))
      (E := (cell13135 ⟨22, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41653877659807 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275108861513 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_23 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41636702252929 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275109365991 / 12500000000000 : ℝ))
      (E := (cell13135 ⟨23, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41636702252929 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275109365991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_24 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41619538874951 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100439458689 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨24, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41619538874951 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100439458689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_25 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83204775019431 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100441490051 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨25, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83204775019431 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100441490051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_26 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83170496282297 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200886943399 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨26, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83170496282297 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200886943399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_27 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41568120753257 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200890984961 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨27, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41568120753257 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200890984961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_28 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83102010660263 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550223747497 / 25000000000000 : ℝ))
      (E := (cell13135 ⟨28, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83102010660263 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550223747497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_29 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (20766950927971 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200899018859 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨29, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (20766950927971 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200899018859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_30 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (2075840515747 / 2500000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (220090301471 / 10000000000000 : ℝ))
      (E := (cell13135 ⟨30, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (2075840515747 / 2500000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (220090301471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_31 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41499730691457 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200907037507 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨31, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41499730691457 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200907037507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_32 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (2592666435619 / 3125000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550227772121 / 25000000000000 : ℝ))
      (E := (cell13135 ⟨32, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (2592666435619 / 3125000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550227772121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_33 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82931214269543 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100457525699 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨33, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82931214269543 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100457525699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_34 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82897126341257 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100459551417 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨34, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82897126341257 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100459551417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_35 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41431531062123 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100461563037 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨35, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41431531062123 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100461563037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_36 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82829021587959 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275115890173 / 12500000000000 : ℝ))
      (E := (cell13135 ⟨36, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82829021587959 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275115890173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_37 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82795004702001 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1719477459 / 78125000000 : ℝ))
      (E := (cell13135 ⟨37, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82795004702001 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1719477459 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_38 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82761011436131 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (220093514563 / 10000000000000 : ℝ))
      (E := (cell13135 ⟨38, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82761011436131 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (220093514563 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_39 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (82727041760261 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100469587037 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨39, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (82727041760261 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100469587037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13136_20 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41688257616819 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200751587477 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨20, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41688257616819 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200751587477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_21 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41671058106421 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100377802871 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨21, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41671058106421 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100377802871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_22 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (10413467664371 / 12500000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275094953713 / 12500000000000 : ℝ))
      (E := (cell13136 ⟨22, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (10413467664371 / 12500000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275094953713 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_23 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (8327339050737 / 10000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100381831337 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨23, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (8327339050737 / 10000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100381831337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_24 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41619531878783 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200767649317 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨24, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41619531878783 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200767649317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_25 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41602380516621 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550192912711 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨25, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41602380516621 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550192912711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_26 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83170482302249 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275096958733 / 12500000000000 : ℝ))
      (E := (cell13136 ⟨26, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83170482302249 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275096958733 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_27 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83136227532603 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100389854379 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨27, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83136227532603 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100389854379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_28 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83101996692483 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550195927791 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨28, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83101996692483 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550195927791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_29 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (8306778975023 / 10000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200787737461 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨29, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (8306778975023 / 10000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200787737461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_30 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83033606674347 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (68774741587 / 3125000000000 : ℝ))
      (E := (cell13136 ⟨30, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83033606674347 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (68774741587 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_31 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (82999447433497 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100397875549 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨31, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (82999447433497 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100397875549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_32 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (82965311996501 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (55019994991 / 2500000000000 : ℝ))
      (E := (cell13136 ⟨32, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (82965311996501 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (55019994991 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_33 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41465600166171 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550200940041 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨33, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41465600166171 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550200940041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_34 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (82897112410157 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200807809257 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨34, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (82897112410157 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200807809257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_35 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (82863048199241 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200811830201 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨35, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (82863048199241 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200811830201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_36 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20707251917261 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (110040791163 / 5000000000000 : ℝ))
      (E := (cell13136 ⟨36, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20707251917261 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (110040791163 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_37 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (82794990789171 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200819847193 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨37, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (82794990789171 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200819847193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_38 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41380498764691 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275102980393 / 12500000000000 : ℝ))
      (E := (cell13136 ⟨38, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41380498764691 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275102980393 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_39 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (82727027859587 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550206967369 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨39, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (82727027859587 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550206967369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13137_20 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83376501218799 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100320163351 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨20, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83376501218799 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100320163351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_21 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83342102204169 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100322171011 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨21, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83342102204169 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100322171011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_22 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41653863656229 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (550162090771 / 25000000000000 : ℝ))
      (E := (cell13137 ⟨22, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41653863656229 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (550162090771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_23 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (10409172063877 / 12500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100326196601 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨23, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (10409172063877 / 12500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100326196601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_24 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83239049767363 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200656377039 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨24, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83239049767363 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200656377039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_25 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (16640949409837 / 20000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100330187903 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨25, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (16640949409837 / 20000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100330187903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_26 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83170468324333 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200664392113 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨26, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83170468324333 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200664392113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_27 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41568106780411 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (110033421417 / 5000000000000 : ℝ))
      (E := (cell13137 ⟨27, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41568106780411 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (110033421417 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_28 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83101982726833 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100336214063 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨28, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83101982726833 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100336214063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_29 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (16613555158141 / 20000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200676451849 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨29, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (16613555158141 / 20000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200676451849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_30 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41516796360471 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100340250599 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨30, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41516796360471 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100340250599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_31 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41499716743103 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200684460479 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨31, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41499716743103 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200684460479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_32 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (2074132451383 / 2500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440137701317 / 20000000000000 : ℝ))
      (E := (cell13137 ⟨32, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (2074132451383 / 2500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440137701317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_33 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (16586237279453 / 20000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100346261673 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨33, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (16586237279453 / 20000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100346261673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_34 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (4144854924059 / 5000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200696511471 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨34, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (4144854924059 / 5000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200696511471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_35 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41431517138179 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (55017513253 / 2500000000000 : ℝ))
      (E := (cell13137 ⟨35, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41431517138179 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (55017513253 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_36 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (331315975009 / 400000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (17605636637 / 800000000000 : ℝ))
      (E := (cell13137 ⟨36, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (331315975009 / 400000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (17605636637 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_37 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41397488439231 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200708601377 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨37, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41397488439231 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200708601377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_38 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (5172561476547 / 6250000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440142519039 / 20000000000000 : ℝ))
      (E := (cell13137 ⟨38, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (5172561476547 / 6250000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440142519039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_39 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (82727013961031 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (27508957743 / 1250000000000 : ℝ))
      (E := (cell13137 ⟨39, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (82727013961031 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (27508957743 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13138_20 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (16675297441219 / 20000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200529061707 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨20, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (16675297441219 / 20000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200529061707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_21 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (162777516011 / 195312500000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200533074081 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨21, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (162777516011 / 195312500000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200533074081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_22 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83307713312081 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440107418449 / 20000000000000 : ℝ))
      (E := (cell13138 ⟨22, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83307713312081 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440107418449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_23 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (16654672503359 / 20000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200541119511 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨23, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (16654672503359 / 20000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200541119511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_24 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (20809758944823 / 25000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200545158957 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨24, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (20809758944823 / 25000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200545158957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_25 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83204733067259 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200549154989 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨25, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83204733067259 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200549154989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_26 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83170454348547 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200553168607 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨26, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83170454348547 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200553168607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_27 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83136199591171 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200557202191 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨27, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83136199591171 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200557202191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_28 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83101968763311 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200561199381 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨28, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83101968763311 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200561199381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_29 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83067761833307 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440113044111 / 20000000000000 : ℝ))
      (E := (cell13138 ⟨29, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83067761833307 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440113044111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_30 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83033578769663 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200569208847 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨30, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83033578769663 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200569208847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_31 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82999419541041 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (88022928969 / 4000000000000 : ℝ))
      (E := (cell13138 ⟨31, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82999419541041 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (88022928969 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_32 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (10370660514533 / 12500000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200577267921 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨32, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (10370660514533 / 12500000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200577267921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_33 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82931172464313 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200581282317 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨33, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82931172464313 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200581282317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_34 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41448542277163 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (3520936429 / 160000000000 : ℝ))
      (E := (cell13138 ⟨34, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41448542277163 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (3520936429 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_35 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (82863020355597 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200589284503 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨35, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (82863020355597 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200589284503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_36 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41414489918789 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100296665891 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨36, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41414489918789 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100296665891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_37 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41397481484937 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100298675677 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨37, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41397481484937 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100298675677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_38 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41380484861121 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200601343039 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨38, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41380484861121 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200601343039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_39 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41363500032297 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200605365199 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨39, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41363500032297 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200605365199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13139_20 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83376473195527 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200417850811 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨20, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83376473195527 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200417850811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_21 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83342074193229 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (440084372053 / 20000000000000 : ℝ))
      (E := (cell13139 ⟨21, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83342074193229 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (440084372053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_22 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (41653849656919 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (440085175111 / 20000000000000 : ℝ))
      (E := (cell13139 ⟨22, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (41653849656919 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (440085175111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_23 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83273348524707 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200429899993 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨23, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83273348524707 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200429899993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_24 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83239021793353 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100216968329 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨24, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83239021793353 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100216968329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_25 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (10400589885933 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (440087585991 / 20000000000000 : ℝ))
      (E := (cell13139 ⟨25, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (10400589885933 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (440087585991 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_26 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83170440374891 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100220970443 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨26, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83170440374891 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100220970443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_27 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83136185623649 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550111492957 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨27, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83136185623649 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550111492957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_28 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83101954801917 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200449966423 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨28, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83101954801917 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200449966423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_29 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20766936969509 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200453985049 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨29, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20766936969509 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200453985049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_30 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (8303356482051 / 10000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200458029393 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨30, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (8303356482051 / 10000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200458029393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_31 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82999405598001 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100231021169 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨31, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82999405598001 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100231021169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_32 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20741317544833 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200466025047 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨32, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20741317544833 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200466025047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_33 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20732789633371 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (55011750927 / 2500000000000 : ℝ))
      (E := (cell13139 ⟨33, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20732789633371 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (55011750927 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_34 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (41448535314797 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200474079219 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨34, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (41448535314797 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200474079219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_35 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82863006436959 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550119523337 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨35, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82863006436959 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550119523337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_36 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (82828965925027 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550120519933 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨36, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (82828965925027 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550120519933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_37 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (16558989812681 / 20000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200486097127 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨37, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (16558989812681 / 20000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200486097127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_38 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (1655219116437 / 2000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100245072711 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨38, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (1655219116437 / 2000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100245072711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_39 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (3309079446811 / 4000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100247082759 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨39, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (3309079446811 / 4000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100247082759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13140_20 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (16675291837419 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (137519164731 / 6250000000000 : ℝ))
      (E := (cell13140 ⟨20, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (16675291837419 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (137519164731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_21 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83342060190961 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (220031064223 / 10000000000000 : ℝ))
      (E := (cell13140 ⟨21, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83342060190961 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (220031064223 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_22 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83307685317729 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200314654647 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨22, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83307685317729 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200314654647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_23 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83273334534751 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200318676259 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨23, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83273334534751 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200318676259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_24 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (41619503904773 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (17190021173 / 781250000000 : ℝ))
      (E := (cell13140 ⟨24, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (41619503904773 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (17190021173 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_25 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (416023525549 / 500000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (550081675177 / 25000000000000 : ℝ))
      (E := (cell13140 ⟨25, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (416023525549 / 500000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (550081675177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_26 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (16634085280673 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200330708951 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨26, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (16634085280673 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200330708951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_27 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (16627234331651 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100167368627 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨27, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (16627234331651 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100167368627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_28 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83101940842651 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200338787761 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨28, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83101940842651 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200338787761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_29 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83067733924893 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100171401931 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨29, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83067733924893 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100171401931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_30 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (20758387718371 / 25000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100173393587 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨30, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (20758387718371 / 25000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100173393587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_31 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82999391657087 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (68760962427 / 3125000000000 : ℝ))
      (E := (cell13140 ⟨31, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82999391657087 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (68760962427 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_32 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (3318610249781 / 4000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440070967313 / 20000000000000 : ℝ))
      (E := (cell13140 ⟨32, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (3318610249781 / 4000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440070967313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_33 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (41465572302389 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (110017942313 / 5000000000000 : ℝ))
      (E := (cell13140 ⟨33, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (41465572302389 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (110017942313 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_34 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (16579411341397 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100181413729 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨34, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (16579411341397 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100181413729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_35 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82862992520441 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (220036689799 / 10000000000000 : ℝ))
      (E := (cell13140 ⟨35, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82862992520441 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (220036689799 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_36 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (20707238003649 / 25000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200370882173 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨36, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (20707238003649 / 25000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200370882173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_37 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (16558987031811 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100187448707 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨37, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (16558987031811 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100187448707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_38 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82760941923577 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200378943601 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨38, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82760941923577 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200378943601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_39 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (82726972278073 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200382961637 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨39, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (82726972278073 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200382961637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13141_20 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (83376445180797 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (440039094937 / 20000000000000 : ℝ))
      (E := (cell13141 ⟨20, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (83376445180797 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (440039094937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_21 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41671023095413 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (550049869581 / 25000000000000 : ℝ))
      (E := (cell13141 ⟨21, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41671023095413 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (550049869581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_22 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (10413458915469 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (550050871973 / 25000000000000 : ℝ))
      (E := (cell13141 ⟨22, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (10413458915469 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (550050871973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_23 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (83273320546927 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200207506701 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨23, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (83273320546927 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200207506701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_24 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (8323899382787 / 10000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (220021153783 / 10000000000000 : ℝ))
      (E := (cell13141 ⟨24, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (8323899382787 / 10000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (220021153783 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_25 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41602345567133 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (550053881421 / 25000000000000 : ℝ))
      (E := (cell13141 ⟨25, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41602345567133 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (550053881421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_26 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (83170412433967 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100109765633 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨26, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (83170412433967 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100109765633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_27 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (8313615769499 / 10000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200223556951 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨27, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (8313615769499 / 10000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200223556951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_28 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (10387740860689 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200227604889 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨28, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (10387740860689 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200227604889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_29 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (664541759791 / 800000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200231618467 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨29, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (664541759791 / 800000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200231618467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_30 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41516768464291 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100117799651 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨30, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41516768464291 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100117799651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_31 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (82999377718297 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (6875748773 / 312500000000 : ℝ))
      (E := (cell13141 ⟨31, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (82999377718297 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (6875748773 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_32 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (518532764449 / 625000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100121821939 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨32, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (518532764449 / 625000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100121821939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_33 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41465565339097 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100123825617 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨33, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41465565339097 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100123825617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_34 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (82897042786497 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200251688789 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨34, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (82897042786497 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200251688789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_35 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20715744651511 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100127849213 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨35, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20715744651511 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100127849213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_36 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20707234526571 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200259680411 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨36, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20707234526571 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200259680411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_37 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (10349365157103 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200263693499 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨37, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (10349365157103 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200263693499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_38 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41380464013711 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200267737579 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨38, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41380464013711 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200267737579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_39 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20681739596997 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100135876777 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨39, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20681739596997 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100135876777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13142_20 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83376431176633 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137505269341 / 6250000000000 : ℝ))
      (E := (cell13142 ⟨20, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83376431176633 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137505269341 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_21 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (3333681287713 / 4000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (11000441551 / 500000000000 : ℝ))
      (E := (cell13142 ⟨21, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (3333681287713 / 4000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (11000441551 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_22 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (20826914332977 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (55002307923 / 2500000000000 : ℝ))
      (E := (cell13142 ⟨22, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (20826914332977 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (55002307923 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_23 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (16654661312247 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200096332927 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨23, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (16654661312247 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200096332927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_24 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (20809744962081 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100050180651 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨24, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (20809744962081 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100050180651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_25 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83204677160861 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137506521653 / 6250000000000 : ℝ))
      (E := (cell13142 ⟨25, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83204677160861 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137506521653 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_26 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83170398466699 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200108407827 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨26, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83170398466699 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200108407827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_27 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (20784035933463 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200112372437 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨27, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (20784035933463 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200112372437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_28 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (166203825861 / 200000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100058208903 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨28, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (166203825861 / 200000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100058208903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_29 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83067706024983 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200120428861 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨29, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83067706024983 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200120428861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_30 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (41516761492903 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100062232887 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨30, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (41516761492903 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100062232887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_31 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (8299936378163 / 10000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200128471427 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨31, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (8299936378163 / 10000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200128471427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_32 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82965228381279 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100066223491 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨32, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82965228381279 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100066223491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_33 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82931116753733 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100068255313 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨33, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82931116753733 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100068255313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_34 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82897028868131 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440028097453 / 20000000000000 : ℝ))
      (E := (cell13142 ⟨34, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82897028868131 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440028097453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_35 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (82862964693767 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100072247329 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨35, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (82862964693767 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100072247329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_36 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (20707231050023 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200148533139 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨36, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (20707231050023 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200148533139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_37 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (10349363419589 / 12500000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100076272049 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨37, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (10349363419589 / 12500000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100076272049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_38 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (10345114266673 / 12500000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137509786631 / 6250000000000 : ℝ))
      (E := (cell13142 ⟨38, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (10345114266673 / 12500000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137509786631 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_39 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (4136347225001 / 5000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440032120007 / 20000000000000 : ℝ))
      (E := (cell13142 ⟨39, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (4136347225001 / 5000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440032120007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13143_20 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83376417174603 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199973140011 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨20, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83376417174603 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199973140011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_21 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83342018196957 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199977137861 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨21, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83342018196957 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199977137861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_22 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (20826910835549 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199981200101 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨22, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (20826910835549 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199981200101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_23 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83273292577673 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199985213333 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨23, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83273292577673 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199985213333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_24 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (20809741467727 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (34374831859 / 1562500000000 : ℝ))
      (E := (cell13143 ⟨24, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (20809741467727 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (34374831859 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_25 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41602331594793 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199993221437 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨25, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41602331594793 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199993221437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_26 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41585192250779 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199997221719 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨26, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41585192250779 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199997221719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_27 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83136129774841 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100000621099 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨27, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83136129774841 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100000621099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_28 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41550949488807 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100002642511 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨28, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41550949488807 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100002642511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_29 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83067692078217 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200009293579 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨29, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83067692078217 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200009293579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_30 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41516754522577 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200013328039 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨30, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41516754522577 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200013328039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_31 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82999349847087 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200017331287 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨31, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82999349847087 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200017331287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_32 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (2074130361321 / 2500000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200021304483 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨32, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (2074130361321 / 2500000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200021304483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_33 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82931102831393 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100012682907 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨33, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82931102831393 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100012682907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_34 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (16579402990377 / 20000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100014670093 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨34, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (16579402990377 / 20000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100014670093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_35 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (8286295078361 / 10000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200033404031 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨35, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (8286295078361 / 10000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200033404031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_36 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82828910296019 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100018690833 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨36, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82828910296019 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100018690833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_37 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82794893458717 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200041390497 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨37, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82794893458717 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200041390497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_38 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (82760900241463 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100022715207 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨38, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (82760900241463 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1100022715207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_39 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (10340866326771 / 12500000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200049442317 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨39, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (10340866326771 / 12500000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2200049442317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13144_20 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83376403174707 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199862024671 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨20, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83376403174707 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199862024671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_21 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (4167100210161 / 5000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199866019653 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨21, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (4167100210161 / 5000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199866019653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_22 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (16661525870923 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (219987007907 / 10000000000000 : ℝ))
      (E := (cell13144 ⟨22, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (16661525870923 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (219987007907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_23 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41636639298121 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (87994963581 / 4000000000000 : ℝ))
      (E := (cell13144 ⟨23, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41636639298121 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (87994963581 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_24 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83238951895621 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199878112439 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨24, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83238951895621 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199878112439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_25 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41602324610219 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099941046109 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨25, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41602324610219 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099941046109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_26 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (16634074107709 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099943044931 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨26, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (16634074107709 / 20000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099943044931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_27 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83136115817957 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (8799560431 / 400000000000 : ℝ))
      (E := (cell13144 ⟨27, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83136115817957 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (8799560431 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_28 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83101885026853 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199894148031 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨28, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83101885026853 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199894148031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_29 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (3322707125343 / 4000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (219989815409 / 10000000000000 : ℝ))
      (E := (cell13144 ⟨29, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (3322707125343 / 4000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (219989815409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_30 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41516747553313 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199902186099 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨30, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41516747553313 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199902186099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_31 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82999335914667 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099953093471 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨31, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82999335914667 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099953093471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_32 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82965200526523 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099955108191 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨32, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82965200526523 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099955108191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_33 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41465544455587 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199914216799 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨33, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41465544455587 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199914216799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_34 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82897001037759 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099959123777 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨34, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82897001037759 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099959123777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_35 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (20715734218893 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199922250531 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨35, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (20715734218893 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199922250531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_36 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (5176806024629 / 6250000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199926284687 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨36, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (5176806024629 / 6250000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199926284687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_37 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (2069871989071 / 2500000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (439986058283 / 20000000000000 : ℝ))
      (E := (cell13144 ⟨37, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (2069871989071 / 2500000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (439986058283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_38 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41380443175829 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (87997373171 / 4000000000000 : ℝ))
      (E := (cell13144 ⟨38, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41380443175829 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (87997373171 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_39 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (82726916730431 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199938339167 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨39, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (82726916730431 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199938339167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13145_20 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83376389176943 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199750905119 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨20, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83376389176943 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199750905119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_21 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (2604437194113 / 3125000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (274969369447 / 12500000000000 : ℝ))
      (E := (cell13145 ⟨21, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (2604437194113 / 3125000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (274969369447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_22 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (16661523073833 / 20000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199758953827 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨22, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (16661523073833 / 20000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199758953827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_23 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83273264616941 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199762961507 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨23, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83273264616941 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199762961507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_24 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (2601216810077 / 3125000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199766981691 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨24, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (2601216810077 / 3125000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199766981691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_25 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83204635253419 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099885508613 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨25, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83204635253419 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099885508613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_26 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83170356577659 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099887506129 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨26, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83170356577659 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099887506129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_27 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83136101863199 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (109988951379 / 5000000000000 : ℝ))
      (E := (cell13145 ⟨27, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83136101863199 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (109988951379 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_28 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41550935539109 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099891532671 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨28, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41550935539109 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099891532671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_29 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41533832095529 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199787068927 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨29, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41533832095529 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199787068927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_30 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83033481170221 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199791098509 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨30, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83033481170221 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199791098509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_31 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (8299932198437 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199795096971 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨31, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (8299932198437 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199795096971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_32 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (10370648325291 / 12500000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199799124077 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨32, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (10370648325291 / 12500000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199799124077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_33 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (20732768748269 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199803122207 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨33, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (20732768748269 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199803122207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_34 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82896987125753 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (3437198673 / 156250000000 : ℝ))
      (E := (cell13145 ⟨34, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82896987125753 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (3437198673 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_35 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82862922969653 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199811151501 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨35, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82862922969653 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199811151501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_36 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82828882494227 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199815183509 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨36, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82828882494227 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199815183509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_37 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (82794865669079 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (439963837627 / 20000000000000 : ℝ))
      (E := (cell13145 ⟨37, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (82794865669079 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (439963837627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_38 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (8276087246397 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099911611969 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨38, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (8276087246397 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099911611969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_39 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (8272690284881 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199827231819 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨39, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (8272690284881 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199827231819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13146_20 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83376375181311 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099819919837 / 50000000000000 : ℝ))
      (E := (cell13146 ⟨20, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83376375181311 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099819919837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_21 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83341976222143 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199643828943 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨21, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83341976222143 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199643828943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_22 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (16661520277169 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (109982394137 / 5000000000000 : ℝ))
      (E := (cell13146 ⟨22, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (16661520277169 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (109982394137 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_23 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83273250639769 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199651887669 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨23, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83273250639769 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199651887669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_24 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (16647784790287 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199655905149 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨24, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (16647784790287 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199655905149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_25 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (5200288830533 / 6250000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (87986397521 / 4000000000000 : ℝ))
      (E := (cell13146 ⟨25, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (5200288830533 / 6250000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (87986397521 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_26 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (831703426189 / 1000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439932786089 / 20000000000000 : ℝ))
      (E := (cell13146 ⟨26, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (831703426189 / 1000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439932786089 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_27 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83136087910567 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199667943203 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨27, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83136087910567 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199667943203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_28 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (20775464282927 / 25000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439934395689 / 20000000000000 : ℝ))
      (E := (cell13146 ⟨28, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (20775464282927 / 25000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439934395689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_29 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (10383456281333 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099837989779 / 50000000000000 : ℝ))
      (E := (cell13146 ⟨29, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (10383456281333 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099837989779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_30 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83033467235939 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439936001343 / 20000000000000 : ℝ))
      (E := (cell13146 ⟨30, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83033467235939 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439936001343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_31 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41499654028097 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199684002797 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨31, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41499654028097 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199684002797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_32 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41482586340127 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199688027569 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨32, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41482586340127 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199688027569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_33 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41465530538549 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549923005853 / 25000000000000 : ℝ))
      (E := (cell13146 ⟨33, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41465530538549 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549923005853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_34 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41448486607933 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439939209937 / 20000000000000 : ℝ))
      (E := (cell13146 ⟨34, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41448486607933 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439939209937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_35 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (20715727266463 / 25000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (137481253017 / 6250000000000 : ℝ))
      (E := (cell13146 ⟨35, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (20715727266463 / 25000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (137481253017 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_36 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82828868596507 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549926019533 / 25000000000000 : ℝ))
      (E := (cell13146 ⟨36, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82828868596507 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549926019533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_37 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (20698712944359 / 25000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439941616131 / 20000000000000 : ℝ))
      (E := (cell13146 ⟨37, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (20698712944359 / 25000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (439941616131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_38 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82760858578397 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199712114403 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨38, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82760858578397 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199712114403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_39 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (82726888969303 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (87988644811 / 4000000000000 : ℝ))
      (E := (cell13146 ⟨39, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (82726888969303 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (87988644811 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13147_20 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83376361187811 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099764385009 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨20, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83376361187811 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099764385009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_21 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83341962234801 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199532814787 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨21, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83341962234801 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199532814787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_22 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16661517480931 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549884201861 / 25000000000000 : ℝ))
      (E := (cell13147 ⟨22, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16661517480931 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549884201861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_23 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41636618332363 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099770404811 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨23, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41636618332363 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099770404811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_24 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41619454991267 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099772412199 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨24, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41619454991267 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099772412199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_25 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83204607325763 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099774427309 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨25, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83204607325763 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099774427309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_26 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83170328662267 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099776422213 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨26, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83170328662267 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099776422213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_27 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (4156803698003 / 5000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (109977842731 / 5000000000000 : ℝ))
      (E := (cell13147 ⟨27, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (4156803698003 / 5000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (109977842731 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_28 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41550921593661 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (137472555459 / 6250000000000 : ℝ))
      (E := (cell13147 ⟨28, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41550921593661 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (137472555459 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_29 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41533818156197 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099782442993 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨29, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41533818156197 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099782442993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_30 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83033453303779 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099784455359 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨30, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83033453303779 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099784455359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_31 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (4149964706507 / 5000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199572963 / 100000000000 : ℝ))
      (E := (cell13147 ⟨31, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (4149964706507 / 5000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199572963 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_32 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (829651587603 / 1000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199576985463 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨32, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (829651587603 / 1000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199576985463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_33 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (2073276179081 / 2500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099790489521 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨33, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (2073276179081 / 2500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099790489521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_34 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41448479654049 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199585003099 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨34, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41448479654049 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199585003099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_35 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82862895164169 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549897249879 / 25000000000000 : ℝ))
      (E := (cell13147 ⟨35, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82862895164169 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549897249879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_36 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (10353606837613 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549898256813 / 25000000000000 : ℝ))
      (E := (cell13147 ⟨36, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (10353606837613 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (549898256813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_37 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (20698709471977 / 25000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099798513849 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨37, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (20698709471977 / 25000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099798513849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_38 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82760844694939 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099800529707 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨38, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82760844694939 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099800529707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_39 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (82726875091909 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099802531651 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨39, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (82726875091909 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099802531651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13148_20 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (83376347196443 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199417754471 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨20, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (83376347196443 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199417754471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_21 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (83341948249589 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199421738077 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨21, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (83341948249589 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199421738077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_22 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41653786712797 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099712893153 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨22, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41653786712797 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099712893153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_23 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (20818305672953 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099714892879 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨23, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (20818305672953 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099714892879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_24 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (1040486200197 / 1250000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439886759571 / 20000000000000 : ℝ))
      (E := (cell13148 ⟨24, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (1040486200197 / 1250000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439886759571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_25 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41602296682563 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (13746486409 / 625000000000 : ℝ))
      (E := (cell13148 ⟨25, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41602296682563 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (13746486409 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_26 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (1039628933847 / 1250000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199441812663 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨26, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (1039628933847 / 1250000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199441812663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_27 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41568030005839 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549861455079 / 25000000000000 : ℝ))
      (E := (cell13148 ⟨27, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41568030005839 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549861455079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_28 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (4155091462253 / 5000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199449850547 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨28, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (4155091462253 / 5000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199449850547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_29 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (83067622376247 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199453846741 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨29, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (83067622376247 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199453846741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_30 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41516719686871 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (137466116817 / 6250000000000 : ℝ))
      (E := (cell13148 ⟨30, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41516719686871 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (137466116817 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_31 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82999280206207 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199461919 / 100000000000 : ℝ))
      (E := (cell13148 ⟨31, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82999280206207 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199461919 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_32 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82965144842467 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439893187831 / 20000000000000 : ℝ))
      (E := (cell13148 ⟨32, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82965144842467 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439893187831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_33 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82931033251501 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199469930473 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨33, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82931033251501 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199469930473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_34 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (5181059087653 / 6250000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099736976157 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨34, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (5181059087653 / 6250000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099736976157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_35 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82862881264603 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099738973281 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨35, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82862881264603 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099738973281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_36 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (82828840807417 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (137467623261 / 6250000000000 : ℝ))
      (E := (cell13148 ⟨36, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (82828840807417 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (137467623261 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_37 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (16558964800099 / 20000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439897194109 / 20000000000000 : ℝ))
      (E := (cell13148 ⟨37, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (16558964800099 / 20000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439897194109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_38 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (16552166162719 / 20000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199490000231 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨38, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (16552166162719 / 20000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199490000231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_39 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (8272686121663 / 10000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099747001067 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨39, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (8272686121663 / 10000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099747001067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13149_20 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (16675266641441 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549826683679 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨20, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (16675266641441 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549826683679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_21 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83341934266507 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199310715503 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨21, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83341934266507 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199310715503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_22 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83307559448663 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1718214657 / 78125000000 : ℝ))
      (E := (cell13149 ⟨22, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83307559448663 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1718214657 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_23 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (3330928348841 / 4000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (274914844711 / 12500000000000 : ℝ))
      (E := (cell13149 ⟨23, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (3330928348841 / 4000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (274914844711 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_24 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41619441025557 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439864553421 / 20000000000000 : ℝ))
      (E := (cell13149 ⟨24, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41619441025557 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439864553421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_25 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41602289703307 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199326792059 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨25, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41602289703307 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199326792059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_26 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41585150377689 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439866155339 / 20000000000000 : ℝ))
      (E := (cell13149 ⟨26, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41585150377689 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439866155339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_27 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (4156802303271 / 5000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439866968059 / 20000000000000 : ℝ))
      (E := (cell13149 ⟨27, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (4156802303271 / 5000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439866968059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_28 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83101815304921 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549834702387 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨28, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83101815304921 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549834702387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_29 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41533804221111 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549835715457 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨29, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41533804221111 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549835715457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_30 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41516712722913 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099673440891 / 50000000000000 : ℝ))
      (E := (cell13149 ⟨30, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41516712722913 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099673440891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_31 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (16599853256879 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199350870801 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨31, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (16599853256879 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199350870801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_32 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (82965130926753 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (274919361081 / 12500000000000 : ℝ))
      (E := (cell13149 ⟨32, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (82965130926753 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (274919361081 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_33 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (2073275483547 / 2500000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549839734083 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨33, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (2073275483547 / 2500000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549839734083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_34 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20724232874729 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549840724333 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨34, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20724232874729 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549840724333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_35 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41431433683577 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439873389617 / 20000000000000 : ℝ))
      (E := (cell13149 ⟨35, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41431433683577 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439873389617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_36 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41414413458023 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (5498427429 / 250000000000 : ℝ))
      (E := (cell13149 ⟨36, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41414413458023 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (5498427429 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_37 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (82794810115197 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549843741979 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨37, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (82794810115197 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549843741979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_38 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41380408467183 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549844748899 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨38, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41380408467183 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549844748899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_39 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (10340855917933 / 12500000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199382995539 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨39, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (10340855917933 / 12500000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199382995539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

end BstLean.Part268
