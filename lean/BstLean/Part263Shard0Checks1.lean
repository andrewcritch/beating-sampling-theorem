import BstLean.Part263Shard0Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12225_20 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20846390866209 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (92606283943 / 4000000000000 : ℝ))
      (E := (cell12225 ⟨20, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20846390866209 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (92606283943 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_21 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83350928207697 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (46303222423 / 2000000000000 : ℝ))
      (E := (cell12225 ⟨21, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83350928207697 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (46303222423 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_22 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (41658158701337 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157582558371 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨22, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (41658158701337 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157582558371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_23 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83281731016457 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578792272483 / 25000000000000 : ℝ))
      (E := (cell12225 ⟨23, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83281731016457 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578792272483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_24 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83247169015907 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (115758655169 / 5000000000000 : ℝ))
      (E := (cell12225 ⟨24, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83247169015907 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (115758655169 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_25 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83212631368057 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157588551457 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨25, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83212631368057 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157588551457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_26 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83178118040109 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315181092397 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨26, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83178118040109 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315181092397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_27 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (41571814499717 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315185075459 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨27, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (41571814499717 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315185075459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_28 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20777291053393 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (231518905549 / 10000000000000 : ℝ))
      (E := (cell12225 ⟨28, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20777291053393 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (231518905549 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_29 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (83074723650229 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315193035651 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨29, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (83074723650229 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315193035651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_30 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20760076819319 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157598509433 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨30, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20760076819319 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157598509433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_31 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (20751478765687 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578800266579 / 25000000000000 : ℝ))
      (E := (cell12225 ⟨31, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (20751478765687 / 25000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578800266579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_32 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82971546974847 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157602502501 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨32, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82971546974847 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157602502501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_33 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (41468601490967 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (289401126577 / 12500000000000 : ℝ))
      (E := (cell12225 ⟨33, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (41468601490967 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (289401126577 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_34 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (41451441526267 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315213032673 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨34, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (41451441526267 / 50000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315213032673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_35 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (82868587155331 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315217008367 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨35, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (82868587155331 / 100000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315217008367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_36 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (8283431525917 / 10000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157610499889 / 50000000000000 : ℝ))
      (E := (cell12225 ⟨36, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (8283431525917 / 10000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (1157610499889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_37 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (16560013466611 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315225008223 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨37, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (16560013466611 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315225008223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_38 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (16553168669229 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578807244037 / 25000000000000 : ℝ))
      (E := (cell12225 ⟨38, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (16553168669229 / 20000000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (578807244037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12225_39 : CellCertificate 12225 (450227846321489 / 5000000000000000 : ℝ) (1718175626812061 / 1000000000000000000 : ℝ) (347397722670537 / 10000000000000000 : ℝ)
    (cell12225 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · norm_num [cell12225]
  · have h := gap_lower (n := 12225) (a := (1034145540847 / 1250000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315232963023 / 100000000000000 : ℝ))
      (E := (cell12225 ⟨39, by decide⟩).energy) (xi := (347397722670537 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12225 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12225]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12225])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12225) (a := (1034145540847 / 1250000000000 : ℝ)) (b := (168573401311 / 100000000000000 : ℝ)) (q := (2315232963023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12225])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12225]

theorem cert12226_20 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (20846388458943 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578751911959 / 25000000000000 : ℝ))
      (E := (cell12226 ⟨20, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (20846388458943 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578751911959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_21 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83350918908659 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578752919581 / 25000000000000 : ℝ))
      (E := (cell12226 ⟨21, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83350918908659 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578752919581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_22 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83316308433199 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289376960327 / 12500000000000 : ℝ))
      (E := (cell12226 ⟨22, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83316308433199 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289376960327 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_23 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83281722376083 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289377458161 / 12500000000000 : ℝ))
      (E := (cell12226 ⟨23, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83281722376083 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289377458161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_24 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41623580352087 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (57875590767 / 2500000000000 : ℝ))
      (E := (cell12226 ⟨24, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41623580352087 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (57875590767 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_25 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41606311692253 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578756910309 / 25000000000000 : ℝ))
      (E := (cell12226 ⟨25, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41606311692253 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (578756910309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_26 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83178110384281 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315031642523 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨26, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83178110384281 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315031642523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_27 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83143621670873 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315035638167 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨27, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83143621670873 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315035638167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_28 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (4155457860591 / 5000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (57875990789 / 2500000000000 : ℝ))
      (E := (cell12226 ⟨28, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (4155457860591 / 5000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (57875990789 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_29 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (8307471697483 / 10000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315043625861 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨29, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (8307471697483 / 10000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315043625861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_30 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (2595009403993 / 3125000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289380952999 / 12500000000000 : ℝ))
      (E := (cell12226 ⟨30, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (2595009403993 / 3125000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (289380952999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_31 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (83005909038693 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315051570161 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨31, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (83005909038693 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315051570161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_32 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (10371442659473 / 12500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157527791889 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨32, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (10371442659473 / 12500000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157527791889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_33 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (8293719760741 / 10000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157529775039 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨33, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (8293719760741 / 10000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157529775039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_34 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41451439001049 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (463012717621 / 20000000000000 : ℝ))
      (E := (cell12226 ⟨34, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41451439001049 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (463012717621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_35 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82868582428533 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315067582541 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨35, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82868582428533 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315067582541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_36 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82834310855559 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157535767431 / 50000000000000 : ℝ))
      (E := (cell12226 ⟨36, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82834310855559 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (1157535767431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_37 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (82800063252183 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315075563569 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨37, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (82800063252183 / 100000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315075563569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_38 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (20691459896891 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315079552527 / 100000000000000 : ℝ))
      (E := (cell12226 ⟨38, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (20691459896891 / 25000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (2315079552527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12226_39 : CellCertificate 12226 (450212816205331 / 5000000000000000 : ℝ) (343607008849341 / 200000000000000000 : ℝ) (347368541485789 / 10000000000000000 : ℝ)
    (cell12226 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · norm_num [cell12226]
  · have h := gap_lower (n := 12226) (a := (41365819915511 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (463016712241 / 20000000000000 : ℝ))
      (E := (cell12226 ⟨39, by decide⟩).energy) (xi := (347368541485789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12226 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12226]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12226])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12226) (a := (41365819915511 / 50000000000000 : ℝ)) (b := (168559427229 / 100000000000000 : ℝ)) (q := (463016712241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12226])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12226]

theorem cert12227_20 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83385544208537 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314858309027 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨20, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83385544208537 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314858309027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_21 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83350909611407 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314862289269 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨21, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83350909611407 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314862289269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_22 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (20829074866367 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314866302327 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨22, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (20829074866367 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314866302327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_23 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (20820428434353 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578717573637 / 25000000000000 : ℝ))
      (E := (cell12227 ⟨23, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (20820428434353 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578717573637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_24 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83247152394103 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (231487427027 / 10000000000000 : ℝ))
      (E := (cell12227 ⟨24, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83247152394103 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (231487427027 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_25 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (3328504616103 / 4000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314878291939 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨25, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (3328504616103 / 4000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314878291939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_26 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83178102730033 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314882246749 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨26, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83178102730033 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314882246749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_27 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83143614343849 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157443127521 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨27, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83143614343849 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157443127521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_28 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (16621830042313 / 20000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157445130931 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨28, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (16621830042313 / 20000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157445130931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_29 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83074710300887 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (72340445949 / 3125000000000 : ℝ))
      (E := (cell12227 ⟨29, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83074710300887 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (72340445949 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_30 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (8304029457969 / 10000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314898225019 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨30, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (8304029457969 / 10000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314898225019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_31 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (83005903016011 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (231490224541 / 10000000000000 : ℝ))
      (E := (cell12227 ⟨31, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (83005903016011 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (231490224541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_32 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (20742883894513 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314906217051 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨32, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (20742883894513 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314906217051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_33 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82937192234177 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578727550159 / 25000000000000 : ℝ))
      (E := (cell12227 ⟨33, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82937192234177 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578727550159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_34 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (5181429559557 / 6250000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578728549541 / 25000000000000 : ℝ))
      (E := (cell12227 ⟨34, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (5181429559557 / 6250000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578728549541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_35 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82868577702943 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (144682388213 / 6250000000000 : ℝ))
      (E := (cell12227 ⟨35, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82868577702943 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (144682388213 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_36 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82834306453117 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578730545827 / 25000000000000 : ℝ))
      (E := (cell12227 ⟨36, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82834306453117 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (578730545827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_37 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82800059172439 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314926173739 / 100000000000000 : ℝ))
      (E := (cell12227 ⟨37, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82800059172439 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (2314926173739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_38 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (82765835830071 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157465091897 / 50000000000000 : ℝ))
      (E := (cell12227 ⟨38, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (82765835830071 / 100000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (1157465091897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12227_39 : CellCertificate 12227 (450197788458709 / 5000000000000000 : ℝ) (171789448468463 / 100000000000000000 : ℝ) (69467873066693 / 2000000000000000 : ℝ)
    (cell12227 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · norm_num [cell12227]
  · have h := gap_lower (n := 12227) (a := (20682909098833 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (115746710717 / 5000000000000 : ℝ))
      (E := (cell12227 ⟨39, by decide⟩).energy) (xi := (69467873066693 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12227 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12227]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12227])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12227) (a := (20682909098833 / 25000000000000 : ℝ)) (b := (33709091099 / 20000000000000 : ℝ)) (q := (115746710717 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12227])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12227]

theorem cert12228_20 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83385534583129 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (289338635269 / 12500000000000 : ℝ))
      (E := (cell12228 ⟨20, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83385534583129 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (289338635269 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_21 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (4167545015797 / 5000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314713070489 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨21, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (4167545015797 / 5000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314713070489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_22 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83316290499481 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (46294340683 / 2000000000000 : ℝ))
      (E := (cell12228 ⟨22, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83316290499481 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (46294340683 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_23 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (20820426275111 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314721036009 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨23, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (20820426275111 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314721036009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_24 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83247144085693 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314725022153 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨24, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83247144085693 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314725022153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_25 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (16642521484453 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314728996677 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨25, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (16642521484453 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314728996677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_26 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83178095077363 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462946604363 / 20000000000000 : ℝ))
      (E := (cell12228 ⟨26, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83178095077363 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462946604363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_27 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83143607018363 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314736984477 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨27, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83143607018363 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314736984477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_28 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (16621828642561 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462948200963 / 20000000000000 : ℝ))
      (E := (cell12228 ⟨28, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (16621828642561 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462948200963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_29 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (83074703628399 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (92589798767 / 4000000000000 : ℝ))
      (E := (cell12228 ⟨29, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (83074703628399 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (92589798767 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_30 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41520144116509 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157374498669 / 50000000000000 : ℝ))
      (E := (cell12228 ⟨30, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41520144116509 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (1157374498669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_31 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (41502948497351 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (231475297509 / 10000000000000 : ℝ))
      (E := (cell12228 ⟨31, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (41502948497351 / 50000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (231475297509 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_32 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (82971529881653 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (231475696333 / 10000000000000 : ℝ))
      (E := (cell12228 ⟨32, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (82971529881653 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (231475696333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_33 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (16587437372447 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314760964289 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨33, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (16587437372447 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314760964289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_34 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (5181429244061 / 6250000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462952995993 / 20000000000000 : ℝ))
      (E := (cell12228 ⟨34, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (5181429244061 / 6250000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (462952995993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_35 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (20717143244641 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314768953547 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨35, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (20717143244641 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314768953547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_36 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (20708575512961 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314772945117 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨36, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (20708575512961 / 25000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314772945117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_37 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (82800055093823 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578694238997 / 25000000000000 : ℝ))
      (E := (cell12228 ⟨37, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (82800055093823 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (578694238997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_38 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (16553166414733 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314780928601 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨38, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (16553166414733 / 20000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314780928601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12228_39 : CellCertificate 12228 (450182763081037 / 5000000000000000 : ℝ) (13419952719689 / 7812500000000000 : ℝ) (347310194212083 / 10000000000000000 : ℝ)
    (cell12228 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · norm_num [cell12228]
  · have h := gap_lower (n := 12228) (a := (82731632960689 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314784922429 / 100000000000000 : ℝ))
      (E := (cell12228 ⟨39, by decide⟩).energy) (xi := (347310194212083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12228 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12228]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12228])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12228) (a := (82731632960689 / 100000000000000 : ℝ)) (b := (168531486109 / 100000000000000 : ℝ)) (q := (2314784922429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12228])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12228]

theorem cert12229_20 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (20846381239887 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314559908983 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨20, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (20846381239887 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314559908983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_21 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (4167544551113 / 5000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314563905481 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨21, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (4167544551113 / 5000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314563905481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_22 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41658140767619 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289320984761 / 12500000000000 : ℝ))
      (E := (cell12229 ⟨22, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41658140767619 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289320984761 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_23 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41640848232589 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92582875587 / 4000000000000 : ℝ))
      (E := (cell12229 ⟨23, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41640848232589 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92582875587 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_24 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16649427155789 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462915165601 / 20000000000000 : ℝ))
      (E := (cell12229 ⟨24, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16649427155789 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462915165601 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_25 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41606299721787 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (144661242009 / 6250000000000 : ℝ))
      (E := (cell12229 ⟨25, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41606299721787 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (144661242009 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_26 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83178087426271 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157291925493 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨26, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83178087426271 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157291925493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_27 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83143599694413 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92583513059 / 4000000000000 : ℝ))
      (E := (cell12229 ⟨27, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83143599694413 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (92583513059 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_28 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (83109136215541 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157295901001 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨28, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (83109136215541 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157295901001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_29 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16614939391473 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314595839163 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨29, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16614939391473 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314595839163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_30 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (1038003523597 / 1250000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314599824023 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨30, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (1038003523597 / 1250000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314599824023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_31 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16601178194953 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314603817689 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨31, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16601178194953 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314603817689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_32 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16594304837317 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157303911309 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨32, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16594304837317 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157303911309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_33 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (647946730403 / 781250000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462922356501 / 20000000000000 : ℝ))
      (E := (cell12229 ⟨33, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (647946730403 / 781250000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462922356501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_34 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (8290286285829 / 10000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314615757837 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨34, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (8290286285829 / 10000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314615757837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_35 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82868568255393 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157309875191 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨35, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82868568255393 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157309875191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_36 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (82834297651739 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462924752337 / 20000000000000 : ℝ))
      (E := (cell12229 ⟨36, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (82834297651739 / 100000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (462924752337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_37 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (16560010203267 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157313896531 / 50000000000000 : ℝ))
      (E := (cell12229 ⟨37, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (16560010203267 / 20000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (1157313896531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_38 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (41382914159173 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289328973369 / 12500000000000 : ℝ))
      (E := (cell12229 ⟨38, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (41382914159173 / 50000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (289328973369 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12229_39 : CellCertificate 12229 (28135483754483 / 312500000000000 : ℝ) (343522686909549 / 200000000000000000 : ℝ) (173640514060081 / 5000000000000000 : ℝ)
    (cell12229 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · norm_num [cell12229]
  · have h := gap_lower (n := 12229) (a := (20682907381773 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314635744149 / 100000000000000 : ℝ))
      (E := (cell12229 ⟨39, by decide⟩).energy) (xi := (173640514060081 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12229 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12229]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12229])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12229) (a := (20682907381773 / 25000000000000 : ℝ)) (b := (16851751907 / 10000000000000 : ℝ)) (q := (2314635744149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12229])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12229]

theorem cert12230_20 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41692757668897 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314410789521 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨20, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41692757668897 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314410789521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_21 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (20837720432591 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314414794247 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨21, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (20837720432591 / 25000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314414794247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_22 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83316272572739 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462883755173 / 20000000000000 : ℝ))
      (E := (cell12230 ⟨22, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83316272572739 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462883755173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_23 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41640843915807 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314422797247 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨23, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41640843915807 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314422797247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_24 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (1300736366779 / 1562500000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314426804477 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨24, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (1300736366779 / 1562500000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314426804477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_25 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41606295733251 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (289303842913 / 12500000000000 : ℝ))
      (E := (cell12230 ⟨25, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41606295733251 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (289303842913 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_26 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41589039888379 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314434734259 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨26, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41589039888379 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314434734259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_27 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (20785898093 / 25000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578609695259 / 25000000000000 : ℝ))
      (E := (cell12230 ⟨27, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (20785898093 / 25000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578609695259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_28 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83109129219773 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314442770259 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨28, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83109129219773 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314442770259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_29 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (16614938057557 / 20000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157223381727 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨29, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (16614938057557 / 20000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157223381727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_30 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (16608055108783 / 20000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578612676269 / 25000000000000 : ℝ))
      (E := (cell12230 ⟨30, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (16608055108783 / 20000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (578612676269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_31 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (83005884956201 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314454714721 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨31, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (83005884956201 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314454714721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_32 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (5185719905803 / 6250000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462891747281 / 20000000000000 : ℝ))
      (E := (cell12230 ⟨32, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (5185719905803 / 6250000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (462891747281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_33 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82937176122223 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314462713821 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨33, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82937176122223 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314462713821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_34 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41451428906427 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157233353727 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨34, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41451428906427 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157233353727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_35 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82868563533431 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (92578828763 / 4000000000000 : ℝ))
      (E := (cell12230 ⟨35, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82868563533431 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (92578828763 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_36 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82834293252801 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314474691621 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨36, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82834293252801 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314474691621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_37 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41400023469987 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314478684963 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨37, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41400023469987 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314478684963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_38 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (82765824564113 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157241350097 / 50000000000000 : ℝ))
      (E := (cell12230 ⟨38, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (82765824564113 / 100000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (1157241350097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12230_39 : CellCertificate 12230 (900305438860391 / 10000000000000000 : ℝ) (34349458879233 / 20000000000000000 : ℝ) (347251867056221 / 10000000000000000 : ℝ)
    (cell12230 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · norm_num [cell12230]
  · have h := gap_lower (n := 12230) (a := (41365813047271 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314486679501 / 100000000000000 : ℝ))
      (E := (cell12230 ⟨39, by decide⟩).energy) (xi := (347251867056221 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12230 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12230]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12230])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12230) (a := (41365813047271 / 50000000000000 : ℝ)) (b := (84251777189 / 50000000000000 : ℝ)) (q := (2314486679501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12230])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12230]

theorem cert12231_20 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (41692752858933 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (578565460057 / 25000000000000 : ℝ))
      (E := (cell12231 ⟨20, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (41692752858933 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (578565460057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_21 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (20837718110063 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314265795043 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨21, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (20837718110063 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314265795043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_22 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83316263611983 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314269785761 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨22, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83316263611983 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314269785761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_23 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (10410209899969 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314273817027 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨23, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (10410209899969 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314273817027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_24 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (20811779792607 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (11571388883 / 500000000000 : ℝ))
      (E := (cell12231 ⟨24, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (20811779792607 / 25000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (11571388883 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_25 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (10401572936381 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157140892599 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨25, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (10401572936381 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157140892599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_26 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83178072128821 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (115714289419 / 5000000000000 : ℝ))
      (E := (cell12231 ⟨26, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83178072128821 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (115714289419 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_27 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83143585051123 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (231428978977 / 10000000000000 : ℝ))
      (E := (cell12231 ⟨27, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83143585051123 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (231428978977 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_28 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (83109122225499 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157146867169 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨28, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (83109122225499 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157146867169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_29 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (4153734180983 / 5000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (72321804439 / 3125000000000 : ℝ))
      (E := (cell12231 ⟨29, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (4153734180983 / 5000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (72321804439 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_30 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (41520134600741 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (578575439357 / 25000000000000 : ℝ))
      (E := (cell12231 ⟨30, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (41520134600741 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (578575439357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_31 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (648483429211 / 781250000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314305724677 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨31, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (648483429211 / 781250000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314305724677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_32 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (41485756400221 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314309704693 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨32, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (41485756400221 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314309704693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_33 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82937170754151 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (289289212463 / 12500000000000 : ℝ))
      (E := (cell12231 ⟨33, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82937170754151 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (289289212463 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_34 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (41451426384333 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157158855853 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨34, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (41451426384333 / 50000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157158855853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_35 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82868558812677 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157160871233 / 50000000000000 : ℝ))
      (E := (cell12231 ⟨35, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82868558812677 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (1157160871233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_36 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (10354286106879 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314325734923 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨36, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (10354286106879 / 12500000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314325734923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_37 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (4140002143237 / 5000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314329690321 / 100000000000000 : ℝ))
      (E := (cell12231 ⟨37, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (4140002143237 / 5000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (2314329690321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_38 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82765820810967 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (231433366833 / 10000000000000 : ℝ))
      (E := (cell12231 ⟨38, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82765820810967 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (231433366833 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12231_39 : CellCertificate 12231 (225068850577927 / 2500000000000000 : ℝ) (214666559544533 / 125000000000000000 : ℝ) (17361135550939 / 500000000000000 : ℝ)
    (cell12231 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · norm_num [cell12231]
  · have h := gap_lower (n := 12231) (a := (82731622663037 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (578584417453 / 25000000000000 : ℝ))
      (E := (cell12231 ⟨39, by decide⟩).energy) (xi := (17361135550939 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12231 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12231]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12231])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12231) (a := (82731622663037 / 100000000000000 : ℝ)) (b := (168489592031 / 100000000000000 : ℝ)) (q := (578584417453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12231])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12231]

theorem cert12232_20 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (20846374024941 / 25000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578528236161 / 25000000000000 : ℝ))
      (E := (cell12232 ⟨20, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (20846374024941 / 25000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578528236161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_21 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (3334034526077 / 4000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314116907867 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨21, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (3334034526077 / 4000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314116907867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_22 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (10414531831621 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314120907777 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨22, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (10414531831621 / 12500000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314120907777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_23 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (8328167056959 / 10000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314124890717 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨23, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (8328167056959 / 10000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314124890717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_24 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83247110868659 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (144633057459 / 6250000000000 : ℝ))
      (E := (cell12232 ⟨24, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83247110868659 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (144633057459 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_25 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83212575517213 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578533220283 / 25000000000000 : ℝ))
      (E := (cell12232 ⟨25, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83212575517213 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (578533220283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_26 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83178064482461 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314136896609 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨26, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83178064482461 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314136896609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_27 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41571788865891 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314140852677 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨27, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41571788865891 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314140852677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_28 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (1038863940409 / 1250000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (231414486949 / 10000000000000 : ℝ))
      (E := (cell12232 ⟨28, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (1038863940409 / 1250000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (231414486949 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_29 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (83074676952987 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314148833389 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨29, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (83074676952987 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314148833389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_30 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41520131430231 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (46283057283 / 2000000000000 : ℝ))
      (E := (cell12232 ⟨30, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41520131430231 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (46283057283 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_31 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41502936461593 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314156847557 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨31, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41502936461593 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314156847557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_32 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41485753554683 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157080422253 / 50000000000000 : ℝ))
      (E := (cell12232 ⟨32, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41485753554683 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157080422253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_33 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (8293716538737 / 10000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314164857223 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨33, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (8293716538737 / 10000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314164857223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_34 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (2590713991429 / 3125000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157084414573 / 50000000000000 : ℝ))
      (E := (cell12232 ⟨34, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (2590713991429 / 3125000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157084414573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_35 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82868554093131 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (462834564111 / 20000000000000 : ℝ))
      (E := (cell12232 ⟨35, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82868554093131 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (462834564111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_36 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82834284458429 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314176832991 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨36, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82834284458429 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314176832991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_37 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (82800038790633 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (144636300571 / 6250000000000 : ℝ))
      (E := (cell12232 ⟨37, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (82800038790633 / 100000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (144636300571 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_38 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (20691454264727 / 25000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314184808663 / 100000000000000 : ℝ))
      (E := (cell12232 ⟨38, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (20691454264727 / 25000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (2314184808663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12232_39 : CellCertificate 12232 (450122685248117 / 5000000000000000 : ℝ) (13415562747859 / 7812500000000000 : ℝ) (347193560006361 / 10000000000000000 : ℝ)
    (cell12232 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · norm_num [cell12232]
  · have h := gap_lower (n := 12232) (a := (41365809616289 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157094386879 / 50000000000000 : ℝ))
      (E := (cell12232 ⟨39, by decide⟩).energy) (xi := (347193560006361 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12232 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12232]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12232])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12232) (a := (41365809616289 / 50000000000000 : ℝ)) (b := (16847563203 / 10000000000000 : ℝ)) (q := (1157094386879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12232])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12232]

theorem cert12233_20 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41692743241743 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156982051387 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨20, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41692743241743 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156982051387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_21 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83350853865381 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156984066361 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨21, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83350853865381 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156984066361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_22 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (5207265355981 / 6250000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313972083637 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨22, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (5207265355981 / 6250000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313972083637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_23 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83281661941129 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313976076617 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨23, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83281661941129 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313976076617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_24 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83247102568549 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156990058033 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨24, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83247102568549 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156990058033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_25 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (16642513508999 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313984089457 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨25, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (16642513508999 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313984089457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_26 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41589028418839 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156994029473 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨26, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41589028418839 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156994029473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_27 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (10392946301747 / 12500000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156996043273 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨27, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (10392946301747 / 12500000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1156996043273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_28 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41554554120717 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313996058883 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨28, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41554554120717 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2313996058883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_29 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83074670287767 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578500009369 / 25000000000000 : ℝ))
      (E := (cell12233 ⟨29, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83074670287767 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578500009369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_30 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (83040256520853 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578501006311 / 25000000000000 : ℝ))
      (E := (cell12233 ⟨30, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (83040256520853 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (578501006311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_31 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (16601173381747 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (18512064199 / 800000000000 : ℝ))
      (E := (cell12233 ⟨31, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (16601173381747 / 20000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (18512064199 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_32 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (4148575070981 / 5000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157006019411 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨32, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (4148575070981 / 5000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157006019411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_33 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82937160021877 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314016010777 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨33, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82937160021877 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314016010777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_34 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82902842684037 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314020001223 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨34, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82902842684037 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314020001223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_35 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (10358568671849 / 12500000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314024011927 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨35, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (10358568671849 / 12500000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314024011927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_36 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (41417140031497 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157013992911 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨36, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (41417140031497 / 50000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157013992911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_37 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (20700008679413 / 25000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157015991391 / 50000000000000 : ℝ))
      (E := (cell12233 ⟨37, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (20700008679413 / 25000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (1157015991391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_38 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (82765813307933 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314036003893 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨38, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (82765813307933 / 100000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314036003893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12233_39 : CellCertificate 12233 (900215343412797 / 10000000000000000 : ℝ) (68682064402603 / 40000000000000000 : ℝ) (86791103504371 / 2500000000000000 : ℝ)
    (cell12233 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · norm_num [cell12233]
  · have h := gap_lower (n := 12233) (a := (20682903950791 / 25000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314039991341 / 100000000000000 : ℝ))
      (E := (cell12233 ⟨39, by decide⟩).energy) (xi := (86791103504371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12233 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12233]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12233])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12233) (a := (20682903950791 / 25000000000000 : ℝ)) (b := (84230837187 / 50000000000000 : ℝ)) (q := (2314039991341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12233])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12233]

theorem cert12234_20 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83385476869033 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313815431077 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨20, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83385476869033 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313815431077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_21 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (4167542229031 / 5000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313819411359 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨21, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (4167542229031 / 5000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313819411359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_22 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41658118370083 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (115691168581 / 5000000000000 : ℝ))
      (E := (cell12234 ⟨22, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41658118370083 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (115691168581 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_23 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (1301275833037 / 1562500000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313827374731 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨23, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (1301275833037 / 1562500000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313827374731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_24 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (41623547135049 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144614460423 / 6250000000000 : ℝ))
      (E := (cell12234 ⟨24, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (41623547135049 / 50000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144614460423 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_25 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16642511914879 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578458837957 / 25000000000000 : ℝ))
      (E := (cell12234 ⟨25, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16642511914879 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578458837957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_26 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83178049194471 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462767866753 / 20000000000000 : ℝ))
      (E := (cell12234 ⟨26, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83178049194471 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462767866753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_27 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (10392945387213 / 12500000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156921687297 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨27, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (10392945387213 / 12500000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156921687297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_28 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (83109101251643 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (289230920117 / 12500000000000 : ℝ))
      (E := (cell12234 ⟨28, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (83109101251643 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (289230920117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_29 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (10384332953 / 12500000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313851354313 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨29, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (10384332953 / 12500000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313851354313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_30 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (81093994319 / 97656250000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156927678821 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨30, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (81093994319 / 97656250000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156927678821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_31 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16601172179131 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (28923241439 / 1250000000000 : ℝ))
      (E := (cell12234 ⟨31, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16601172179131 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (28923241439 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_32 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (20742873932801 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462772669231 / 20000000000000 : ℝ))
      (E := (cell12234 ⟨32, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (20742873932801 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (462772669231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_33 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (82937154657673 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578466833993 / 25000000000000 : ℝ))
      (E := (cell12234 ⟨33, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (82937154657673 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (578466833993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_34 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16580567528719 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156935643247 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨34, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16580567528719 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156935643247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_35 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (82868544657661 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156937658291 / 50000000000000 : ℝ))
      (E := (cell12234 ⟨35, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (82868544657661 / 100000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (1156937658291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_36 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (3313371026749 / 4000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313879310633 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨36, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (3313371026749 / 4000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313879310633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_37 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (20700007661449 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313883269891 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨37, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (20700007661449 / 25000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313883269891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_38 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16553161911609 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313887254021 / 100000000000000 : ℝ))
      (E := (cell12234 ⟨38, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16553161911609 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (2313887254021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12234_39 : CellCertificate 12234 (900185321060227 / 10000000000000000 : ℝ) (1716911211367999 / 1000000000000000000 : ℝ) (347135273050673 / 10000000000000000 : ℝ)
    (cell12234 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · norm_num [cell12234]
  · have h := gap_lower (n := 12234) (a := (16546322474959 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144618203993 / 6250000000000 : ℝ))
      (E := (cell12234 ⟨39, by decide⟩).energy) (xi := (347135273050673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12234 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12234]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12234])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12234) (a := (16546322474959 / 20000000000000 : ℝ)) (b := (168447719061 / 100000000000000 : ℝ)) (q := (144618203993 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12234])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12234]

theorem cert12235_20 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (16677093451281 / 20000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462733350973 / 20000000000000 : ℝ))
      (E := (cell12235 ⟨20, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (16677093451281 / 20000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462733350973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_21 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41675417648821 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156835371889 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨21, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41675417648821 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156835371889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_22 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (10414528473297 / 12500000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (144604673233 / 6250000000000 : ℝ))
      (E := (cell12235 ⟨22, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (10414528473297 / 12500000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (144604673233 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_23 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83281644689307 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156839363379 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨23, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83281644689307 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156839363379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_24 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (16649417194661 / 20000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313682729773 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨24, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (16649417194661 / 20000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313682729773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_25 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (20803137901353 / 25000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231368672659 / 10000000000000 : ℝ))
      (E := (cell12235 ⟨25, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (20803137901353 / 25000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (231368672659 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_26 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83178041552839 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156845360533 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨26, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83178041552839 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156845360533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_27 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83143555782967 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (115684735841 / 5000000000000 : ℝ))
      (E := (cell12235 ⟨27, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83143555782967 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (115684735841 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_28 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (5194318391459 / 6250000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156849358617 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨28, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (5194318391459 / 6250000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156849358617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_29 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41537328480843 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313702725459 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨29, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41537328480843 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313702725459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_30 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (83040243845871 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (46274133719 / 2000000000000 : ℝ))
      (E := (cell12235 ⟨30, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (83040243845871 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (46274133719 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_31 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (16601170976789 / 20000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462742143659 / 20000000000000 : ℝ))
      (E := (cell12235 ⟨31, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (16601170976789 / 20000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462742143659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_32 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82971490044117 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462742941599 / 20000000000000 : ℝ))
      (E := (cell12235 ⟨32, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82971490044117 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (462742941599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_33 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82937149294757 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (115685935787 / 5000000000000 : ℝ))
      (E := (cell12235 ⟨33, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82937149294757 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (115685935787 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_34 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (207257081511 / 250000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156861342481 / 50000000000000 : ℝ))
      (E := (cell12235 ⟨34, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (207257081511 / 250000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (1156861342481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_35 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82868539941737 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (115686333797 / 5000000000000 : ℝ))
      (E := (cell12235 ⟨35, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82868539941737 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (115686333797 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_36 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (41417135637811 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578432672553 / 25000000000000 : ℝ))
      (E := (cell12235 ⟨36, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (41417135637811 / 50000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (578432672553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_37 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82800026575067 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313734670461 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨37, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82800026575067 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313734670461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_38 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (82765805809241 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313738676353 / 100000000000000 : ℝ))
      (E := (cell12235 ⟨38, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (82765805809241 / 100000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (2313738676353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12235_39 : CellCertificate 12235 (112519412929669 / 1250000000000000 : ℝ) (1716770835629093 / 1000000000000000000 : ℝ) (6942122742089 / 200000000000000 : ℝ)
    (cell12235 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · norm_num [cell12235]
  · have h := gap_lower (n := 12235) (a := (8273160894747 / 10000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (92549706003 / 4000000000000 : ℝ))
      (E := (cell12235 ⟨39, by decide⟩).energy) (xi := (6942122742089 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12235 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12235]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12235])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12235) (a := (8273160894747 / 10000000000000 : ℝ)) (b := (42108441523 / 25000000000000 : ℝ)) (q := (92549706003 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12235])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12235]

theorem cert12236_20 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (104231822057 / 125000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (231351824883 / 10000000000000 : ℝ))
      (E := (cell12236 ⟨20, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (104231822057 / 125000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (231351824883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_21 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41675413008223 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462704449297 / 20000000000000 : ℝ))
      (E := (cell12236 ⟨21, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41675413008223 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462704449297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_22 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (83316218834327 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156763112843 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨22, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (83316218834327 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156763112843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_23 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (16656327213189 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (23135302493 / 1000000000000 : ℝ))
      (E := (cell12236 ⟨23, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (16656327213189 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (23135302493 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_24 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (83247077678169 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578383551271 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨24, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (83247077678169 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578383551271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_25 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (16642508727609 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578384553437 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨25, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (16642508727609 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578384553437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_26 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41589016956391 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313542220853 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨26, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41589016956391 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313542220853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_27 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (20785887117441 / 25000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156773085809 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨27, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (20785887117441 / 25000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156773085809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_28 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (83109087276539 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156775093097 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨28, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (83109087276539 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156775093097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_29 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41537325150411 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156777075459 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨29, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41537325150411 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156777075459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_30 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (2595007422203 / 3125000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578389546391 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨30, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (2595007422203 / 3125000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578389546391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_31 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (16601169774721 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (289195271989 / 12500000000000 : ℝ))
      (E := (cell12236 ⟨31, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (16601169774721 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (289195271989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_32 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82971484358359 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462713236571 / 20000000000000 : ℝ))
      (E := (cell12236 ⟨32, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82971484358359 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462713236571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_33 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (8293714393313 / 10000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (7229906719 / 312500000000 : ℝ))
      (E := (cell12236 ⟨33, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (8293714393313 / 10000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (7229906719 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_34 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (20725706891613 / 25000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578393534517 / 25000000000000 : ℝ))
      (E := (cell12236 ⟨34, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (20725706891613 / 25000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (578393534517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_35 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82868535227019 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462715629717 / 20000000000000 : ℝ))
      (E := (cell12236 ⟨35, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82868535227019 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (462715629717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_36 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (16566853376737 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313582124561 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨36, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (16566853376737 / 20000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313582124561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_37 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (82800022505463 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156793062933 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨37, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (82800022505463 / 100000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156793062933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_38 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (41382901030761 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313590094933 / 100000000000000 : ℝ))
      (E := (cell12236 ⟨38, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (41382901030761 / 50000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (2313590094933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12236_39 : CellCertificate 12236 (450062645271501 / 5000000000000000 : ℝ) (68665219313709 / 40000000000000000 : ℝ) (17353850308867 / 500000000000000 : ℝ)
    (cell12236 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · norm_num [cell12236]
  · have h := gap_lower (n := 12236) (a := (8273160552119 / 10000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156797045613 / 50000000000000 : ℝ))
      (E := (cell12236 ⟨39, by decide⟩).energy) (xi := (17353850308867 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12236 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12236]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12236])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12236) (a := (8273160552119 / 10000000000000 : ℝ)) (b := (84209907733 / 50000000000000 : ℝ)) (q := (1156797045613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12236])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12236]

theorem cert12237_20 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41692724018309 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (462673959303 / 20000000000000 : ℝ))
      (E := (cell12237 ⟨20, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41692724018309 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (462673959303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_21 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83350816737031 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313373802979 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨21, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83350816737031 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313373802979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_22 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83316209884019 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313377791771 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨22, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83316209884019 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313377791771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_23 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83281627444281 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156690883731 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨23, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83281627444281 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156690883731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_24 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20811767346173 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (23133857927 / 1000000000000 : ℝ))
      (E := (cell12237 ⟨24, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20811767346173 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (23133857927 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_25 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41606267836147 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578347438739 / 25000000000000 : ℝ))
      (E := (cell12237 ⟨25, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41606267836147 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578347438739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_26 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83178026274301 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313393774753 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨26, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83178026274301 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313393774753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_27 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (16628708231619 / 20000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (144587358687 / 6250000000000 : ℝ))
      (E := (cell12237 ⟨27, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (16628708231619 / 20000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (144587358687 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_28 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41554540145613 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313401767819 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨28, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41554540145613 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313401767819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_29 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (8307464364141 / 10000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578351436893 / 25000000000000 : ℝ))
      (E := (cell12237 ⟨29, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (8307464364141 / 10000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (578351436893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_30 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (83040231176531 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156704869779 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨30, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (83040231176531 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156704869779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_31 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41502921432317 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156706873231 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨31, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41502921432317 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156706873231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_32 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82971478673929 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (92536708489 / 4000000000000 : ℝ))
      (E := (cell12237 ⟨32, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82971478673929 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (92536708489 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_33 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (8293713857279 / 10000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313421697531 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨33, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (8293713857279 / 10000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313421697531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_34 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82902822529751 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156712852187 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨34, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82902822529751 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156712852187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_35 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (20717132628377 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (462685935187 / 20000000000000 : ℝ))
      (E := (cell12237 ⟨35, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (20717132628377 / 25000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (462685935187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_36 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41417131246457 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313433672287 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨36, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41417131246457 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313433672287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_37 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82800018436983 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156718847369 / 50000000000000 : ℝ))
      (E := (cell12237 ⟨37, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82800018436983 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (1156718847369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_38 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (82765798314887 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (57836042143 / 2500000000000 : ℝ))
      (E := (cell12237 ⟨38, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (82765798314887 / 100000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (57836042143 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12237_39 : CellCertificate 12237 (112511910297001 / 1250000000000000 : ℝ) (858245076501633 / 500000000000000000 : ℝ) (86761970066967 / 2500000000000000 : ℝ)
    (cell12237 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · norm_num [cell12237]
  · have h := gap_lower (n := 12237) (a := (41365801047977 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313445646021 / 100000000000000 : ℝ))
      (E := (cell12237 ⟨39, by decide⟩).energy) (xi := (86761970066967 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12237 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12237]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12237])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12237) (a := (41365801047977 / 50000000000000 : ℝ)) (b := (84202933591 / 50000000000000 : ℝ)) (q := (2313445646021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12237])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12237]

theorem cert12238_20 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83385438429459 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (46264429123 / 2000000000000 : ℝ))
      (E := (cell12238 ⟨20, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83385438429459 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (46264429123 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_21 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41675403729699 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (115661270663 / 5000000000000 : ℝ))
      (E := (cell12238 ⟨21, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41675403729699 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (115661270663 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_22 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83316200935449 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (18072104779 / 781250000000 : ℝ))
      (E := (cell12238 ⟨22, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83316200935449 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (18072104779 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_23 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (20820404706079 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156616698921 / 50000000000000 : ℝ))
      (E := (cell12238 ⟨23, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (20820404706079 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156616698921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_24 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (8324706109287 / 10000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462647486861 / 20000000000000 : ℝ))
      (E := (cell12238 ⟨24, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (8324706109287 / 10000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462647486861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_25 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41606263854079 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578310352141 / 25000000000000 : ℝ))
      (E := (cell12238 ⟨25, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41606263854079 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578310352141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_26 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (83178018637393 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313245382773 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨26, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (83178018637393 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313245382773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_27 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41571766923979 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (36144522171 / 1562500000000 : ℝ))
      (E := (cell12238 ⟨27, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41571766923979 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (36144522171 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_28 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (16621814661481 / 20000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313253403693 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨28, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (16621814661481 / 20000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313253403693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_29 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (1661492739669 / 2000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313257398539 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨29, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (1661492739669 / 2000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313257398539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_30 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (10380028105497 / 12500000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578315336983 / 25000000000000 : ℝ))
      (E := (cell12238 ⟨30, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (10380028105497 / 12500000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (578315336983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_31 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (10375729607129 / 12500000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156632685729 / 50000000000000 : ℝ))
      (E := (cell12238 ⟨31, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (10375729607129 / 12500000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156632685729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_32 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82971472990827 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156634677309 / 50000000000000 : ℝ))
      (E := (cell12238 ⟨32, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82971472990827 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (1156634677309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_33 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82937133213737 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462654671619 / 20000000000000 : ℝ))
      (E := (cell12238 ⟨33, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82937133213737 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (462654671619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_34 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82902817494297 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313277325323 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨34, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82902817494297 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313277325323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_35 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (41434262900601 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313281316577 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨35, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (41434262900601 / 50000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313281316577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_36 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (20708564525827 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313285333391 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨36, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (20708564525827 / 25000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313285333391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_37 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82800014369629 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313289318447 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨37, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82800014369629 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313289318447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_38 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82765794569337 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (231329333141 / 10000000000000 : ℝ))
      (E := (cell12238 ⟨38, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82765794569337 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (231329333141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12238_39 : CellCertificate 12238 (1125081598669 / 12500000000000 : ℝ) (171634984610509 / 100000000000000000 : ℝ) (173509379687279 / 5000000000000000 : ℝ)
    (cell12238 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · norm_num [cell12238]
  · have h := gap_lower (n := 12238) (a := (82731598671761 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313297314461 / 100000000000000 : ℝ))
      (E := (cell12238 ⟨39, by decide⟩).energy) (xi := (173509379687279 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12238 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12238]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12238])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12238) (a := (82731598671761 / 100000000000000 : ℝ)) (b := (168391921239 / 100000000000000 : ℝ)) (q := (2313297314461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12238])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12238]

theorem cert12239_20 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41692714412061 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578268292377 / 25000000000000 : ℝ))
      (E := (cell12239 ⟨20, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41692714412061 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578268292377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_21 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (16670159636709 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578269298459 / 25000000000000 : ℝ))
      (E := (cell12239 ⟨21, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (16670159636709 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578269298459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_22 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83316191988619 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313081143783 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨22, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83316191988619 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313081143783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_23 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (2602550318939 / 3125000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578271285111 / 25000000000000 : ℝ))
      (E := (cell12239 ⟨23, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (2602550318939 / 3125000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (578271285111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_24 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41623526401353 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156544564947 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨24, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41623526401353 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156544564947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_25 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41606259872819 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313093116223 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨25, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41606259872819 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313093116223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_26 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83178011002059 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313097161653 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨26, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83178011002059 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313097161653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_27 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (16628705307871 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (57827528827 / 2500000000000 : ℝ))
      (E := (cell12239 ⟨27, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (16628705307871 / 20000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (57827528827 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_28 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (3324362653003 / 4000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156552546909 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨28, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (3324362653003 / 4000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156552546909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_29 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83074630326939 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (144569318989 / 6250000000000 : ℝ))
      (E := (cell12239 ⟨29, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83074630326939 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (144569318989 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_30 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (83040218512831 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (36142392619 / 1562500000000 : ℝ))
      (E := (cell12239 ⟨30, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (83040218512831 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (36142392619 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_31 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41502915425399 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (231311710939 / 10000000000000 : ℝ))
      (E := (cell12239 ⟨31, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41502915425399 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (231311710939 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_32 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41485733654527 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462624222007 / 20000000000000 : ℝ))
      (E := (cell12239 ⟨32, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41485733654527 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (462624222007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_33 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (20734281963993 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313125073237 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨33, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (20734281963993 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313125073237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_34 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (82902812460089 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156564529737 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨34, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (82902812460089 / 100000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156564529737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_35 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41434260545051 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313133070509 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨35, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41434260545051 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313133070509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_36 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41417126857433 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313137049271 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨36, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41417126857433 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313137049271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_37 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (41400005151699 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313141055627 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨37, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (41400005151699 / 50000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313141055627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_38 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (8276579082487 / 10000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156572516003 / 50000000000000 : ℝ))
      (E := (cell12239 ⟨38, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (8276579082487 / 10000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (1156572516003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12239_39 : CellCertificate 12239 (900035280219407 / 10000000000000000 : ℝ) (171620956214257 / 100000000000000000 : ℝ) (346989643495939 / 10000000000000000 : ℝ)
    (cell12239 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · norm_num [cell12239]
  · have h := gap_lower (n := 12239) (a := (20682898812153 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313149037871 / 100000000000000 : ℝ))
      (E := (cell12239 ⟨39, by decide⟩).energy) (xi := (346989643495939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12239 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12239]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12239])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12239) (a := (20682898812153 / 25000000000000 : ℝ)) (b := (168377977637 / 100000000000000 : ℝ)) (q := (2313149037871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12239])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12239]

theorem cert12240_20 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83385419220607 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312924994819 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨20, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83385419220607 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312924994819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_21 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83350788909473 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578232242487 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨21, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83350788909473 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578232242487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_22 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (10414522880441 / 12500000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312932987987 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨22, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (10414522880441 / 12500000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312932987987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_23 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41640800794739 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578234248817 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨23, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41640800794739 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578234248817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_24 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83247044514197 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312940996121 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨24, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83247044514197 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312940996121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_25 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (20803127946183 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (289118124329 / 12500000000000 : ℝ))
      (E := (cell12240 ⟨25, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (20803127946183 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (289118124329 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_26 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83178003368299 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156474468141 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨26, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83178003368299 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156474468141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_27 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83143519232283 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578238235351 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨27, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83143519232283 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578238235351 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_28 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83109059344237 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (231295695503 / 10000000000000 : ℝ))
      (E := (cell12240 ⟨28, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83109059344237 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (231295695503 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_29 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83074623671879 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312960921867 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨29, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83074623671879 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312960921867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_30 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (16608042436619 / 20000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (462592992337 / 20000000000000 : ℝ))
      (E := (cell12240 ⟨30, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (16608042436619 / 20000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (462592992337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_31 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (83005824845933 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (231296890177 / 10000000000000 : ℝ))
      (E := (cell12240 ⟨31, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (83005824845933 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (231296890177 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_32 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82971461628607 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312972919967 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨32, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82971461628607 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312972919967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_33 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82937122499493 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156488450747 / 50000000000000 : ℝ))
      (E := (cell12240 ⟨33, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82937122499493 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (1156488450747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_34 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82902807427127 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312980906829 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨34, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82902807427127 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312980906829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_35 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82868516380207 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (144561554947 / 6250000000000 : ℝ))
      (E := (cell12240 ⟨35, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82868516380207 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (144561554947 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_36 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (8283424932759 / 10000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578247219633 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨36, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (8283424932759 / 10000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578247219633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_37 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (20700001559573 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578248226569 / 25000000000000 : ℝ))
      (E := (cell12240 ⟨37, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (20700001559573 / 25000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (578248226569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_38 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (82765787081487 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312996904813 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨38, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (82765787081487 / 100000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2312996904813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12240_39 : CellCertificate 12240 (900005286227463 / 10000000000000000 : ℝ) (343213860222017 / 200000000000000000 : ℝ) (69392106526107 / 2000000000000000 : ℝ)
    (cell12240 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · norm_num [cell12240]
  · have h := gap_lower (n := 12240) (a := (41365795913253 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313000874929 / 100000000000000 : ℝ))
      (E := (cell12240 ⟨39, by decide⟩).energy) (xi := (69392106526107 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12240 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12240]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12240])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12240) (a := (41365795913253 / 50000000000000 : ℝ)) (b := (1346912291 / 800000000000 : ℝ)) (q := (2313000874929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12240])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12240]

theorem cert12241_20 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83385409618913 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156388466043 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨20, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83385409618913 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156388466043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_21 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (4167538981859 / 5000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312780916359 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨21, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (4167538981859 / 5000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312780916359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_22 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (3332646964007 / 4000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (72274527689 / 3125000000000 : ℝ))
      (E := (cell12241 ⟨22, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (3332646964007 / 4000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (72274527689 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_23 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (16656318594921 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (144549306501 / 6250000000000 : ℝ))
      (E := (cell12241 ⟨23, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (16656318594921 / 20000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (144549306501 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_24 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (5202939764209 / 6250000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312792858013 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨24, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (5202939764209 / 6250000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312792858013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_25 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83212503825441 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578199217187 / 25000000000000 : ℝ))
      (E := (cell12241 ⟨25, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83212503825441 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578199217187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_26 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (5198624733507 / 6250000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156400440887 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨26, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (5198624733507 / 6250000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156400440887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_27 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (10392938990843 / 12500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578201210577 / 25000000000000 : ℝ))
      (E := (cell12241 ⟨27, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (10392938990843 / 12500000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578201210577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_28 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83109052364889 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (72275277203 / 3125000000000 : ℝ))
      (E := (cell12241 ⟨28, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83109052364889 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (72275277203 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_29 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (20768654254567 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312812852671 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨29, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (20768654254567 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312812852671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_30 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (83040205854767 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156408425069 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨30, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (83040205854767 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156408425069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_31 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (20751454710609 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312820865577 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨31, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (20751454710609 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312820865577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_32 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (5185715996843 / 6250000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156412421463 / 50000000000000 : ℝ))
      (E := (cell12241 ⟨32, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (5185715996843 / 6250000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (1156412421463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_33 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (829371171443 / 1000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578207210717 / 25000000000000 : ℝ))
      (E := (cell12241 ⟨33, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (829371171443 / 1000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (578207210717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_34 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (8290280239541 / 10000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312832808831 / 100000000000000 : ℝ))
      (E := (cell12241 ⟨34, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (8290280239541 / 10000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (2312832808831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_35 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (20717127917879 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (231283680109 / 10000000000000 : ℝ))
      (E := (cell12241 ⟨35, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (20717127917879 / 25000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (231283680109 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_36 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82834244941477 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289105102647 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨36, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82834244941477 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289105102647 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_37 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82800002174309 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289105601471 / 12500000000000 : ℝ))
      (E := (cell12241 ⟨37, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82800002174309 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (289105601471 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_38 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (82765783339187 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (18502790191 / 800000000000 : ℝ))
      (E := (cell12241 ⟨38, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (82765783339187 / 100000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (18502790191 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12241_39 : CellCertificate 12241 (449987648479099 / 5000000000000000 : ℝ) (1715929063002011 / 1000000000000000000 : ℝ) (346931426776877 / 10000000000000000 : ℝ)
    (cell12241 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · norm_num [cell12241]
  · have h := gap_lower (n := 12241) (a := (41365794202721 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (28910659587 / 1250000000000 : ℝ))
      (E := (cell12241 ⟨39, by decide⟩).energy) (xi := (346931426776877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12241 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12241]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12241])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12241) (a := (41365794202721 / 50000000000000 : ℝ)) (b := (168350097453 / 100000000000000 : ℝ)) (q := (28910659587 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12241])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12241]

theorem cert12242_20 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83385400019041 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312628923079 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨20, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83385400019041 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312628923079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_21 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41675385183333 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578158229141 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨21, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41675385183333 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578158229141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_22 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (520726032241 / 625000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312636896247 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨22, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (520726032241 / 625000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312636896247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_23 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (20820396090357 / 25000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231264092499 / 10000000000000 : ℝ))
      (E := (cell12242 ⟨23, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (20820396090357 / 25000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231264092499 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_24 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41623513971073 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (144540305659 / 6250000000000 : ℝ))
      (E := (cell12242 ⟨24, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41623513971073 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (144540305659 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_25 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83212495867763 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231264885527 / 10000000000000 : ℝ))
      (E := (cell12242 ⟨25, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83212495867763 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (231264885527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_26 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41588994052749 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312652881389 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨26, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41588994052749 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312652881389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_27 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (5196469038921 / 6250000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578164213949 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨27, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (5196469038921 / 6250000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578164213949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_28 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (10388630673379 / 12500000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (289082605027 / 12500000000000 : ℝ))
      (E := (cell12242 ⟨28, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (10388630673379 / 12500000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (289082605027 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_29 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (83074610366107 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (462532967559 / 20000000000000 : ℝ))
      (E := (cell12242 ⟨29, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (83074610366107 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (462532967559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_30 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (10380024940981 / 12500000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156334425721 / 50000000000000 : ℝ))
      (E := (cell12242 ⟨30, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (10380024940981 / 12500000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (1156334425721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_31 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41502906420153 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578168206337 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨31, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41502906420153 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578168206337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_32 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (16594290054339 / 20000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312676820403 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨32, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (16594290054339 / 20000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312676820403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_33 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82937111790393 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (289085104853 / 12500000000000 : ℝ))
      (E := (cell12242 ⟨33, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82937111790393 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (289085104853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_34 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (41451398682469 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (57817120601 / 2500000000000 : ℝ))
      (E := (cell12242 ⟨34, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (41451398682469 / 50000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (57817120601 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_35 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (8286850696403 / 10000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578172209081 / 25000000000000 : ℝ))
      (E := (cell12242 ⟨35, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (8286850696403 / 10000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (578172209081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_36 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (5177140034783 / 6250000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (11563464093 / 500000000000 : ℝ))
      (E := (cell12242 ⟨36, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (5177140034783 / 6250000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (11563464093 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_37 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (1655999962229 / 2000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312696830733 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨37, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (1655999962229 / 2000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312696830733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_38 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (8276577959797 / 10000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (144543800947 / 6250000000000 : ℝ))
      (E := (cell12242 ⟨38, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (8276577959797 / 10000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (144543800947 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12242_39 : CellCertificate 12242 (899945312410443 / 10000000000000000 : ℝ) (1715788847812729 / 1000000000000000000 : ℝ) (346902325933491 / 10000000000000000 : ℝ)
    (cell12242 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · norm_num [cell12242]
  · have h := gap_lower (n := 12242) (a := (82731584985421 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312704772641 / 100000000000000 : ℝ))
      (E := (cell12242 ⟨39, by decide⟩).energy) (xi := (346902325933491 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12242 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12242]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12242])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12242) (a := (82731584985421 / 100000000000000 : ℝ)) (b := (16833616087 / 10000000000000 : ℝ)) (q := (2312704772641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12242])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12242]

theorem cert12243_20 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (20846347605247 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (144530064127 / 6250000000000 : ℝ))
      (E := (cell12243 ⟨20, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (20846347605247 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (144530064127 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_21 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (20837690274483 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312485028817 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨21, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (20837690274483 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312485028817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_22 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83316156218683 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312489018583 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨22, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83316156218683 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312489018583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_23 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83281575749947 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578123249973 / 25000000000000 : ℝ))
      (E := (cell12243 ⟨23, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83281575749947 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (578123249973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_24 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41623509829301 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (231249697707 / 10000000000000 : ℝ))
      (E := (cell12243 ⟨24, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41623509829301 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (231249697707 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_25 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83212487911699 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312500954199 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨25, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83212487911699 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312500954199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_26 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (16635596095291 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312504993501 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨26, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (16635596095291 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312504993501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_27 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83143497320259 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (231250898187 / 10000000000000 : ℝ))
      (E := (cell12243 ⟨27, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83143497320259 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (231250898187 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_28 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (16621807682133 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312512922611 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨28, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (16621807682133 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312512922611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_29 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (16614920743079 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312516935683 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨29, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (16614920743079 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312516935683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_30 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83040193202337 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2890651207 / 125000000000 : ℝ))
      (E := (cell12243 ⟨30, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83040193202337 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2890651207 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_31 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (83005806839543 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (46250499131 / 2000000000000 : ℝ))
      (E := (cell12243 ⟨31, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (83005806839543 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (46250499131 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_32 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (20742861148807 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (36133264233 / 1562500000000 : ℝ))
      (E := (cell12243 ⟨32, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (20742861148807 / 25000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (36133264233 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_33 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82937106437771 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312532947901 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨33, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82937106437771 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312532947901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_34 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82902792335711 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (23125368939 / 1000000000000 : ℝ))
      (E := (cell12243 ⟨34, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82902792335711 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (23125368939 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_35 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82868502257749 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (36133451973 / 1562500000000 : ℝ))
      (E := (cell12243 ⟨35, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82868502257749 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (36133451973 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_36 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82834236172743 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312544929409 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨36, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82834236172743 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312544929409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_37 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (82799994049713 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (462509780909 / 20000000000000 : ℝ))
      (E := (cell12243 ⟨37, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (82799994049713 / 100000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (462509780909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_38 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (16553155171567 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312552911341 / 100000000000000 : ℝ))
      (E := (cell12243 ⟨38, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (16553155171567 / 20000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (2312552911341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12243_39 : CellCertificate 12243 (899915332583033 / 10000000000000000 : ℝ) (857824327768311 / 500000000000000000 : ℝ) (346873230098909 / 10000000000000000 : ℝ)
    (cell12243 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · norm_num [cell12243]
  · have h := gap_lower (n := 12243) (a := (41365790783221 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (289069611497 / 12500000000000 : ℝ))
      (E := (cell12243 ⟨39, by decide⟩).energy) (xi := (346873230098909 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12243 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12243]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12243])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12243) (a := (41365790783221 / 50000000000000 : ℝ)) (b := (1346577813 / 800000000000 : ℝ)) (q := (289069611497 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12243])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12243]

theorem cert12244_20 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (16677076164951 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578083295679 / 25000000000000 : ℝ))
      (E := (cell12244 ⟨20, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (16677076164951 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578083295679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_21 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (1302355497359 / 1562500000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312337194867 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨21, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (1302355497359 / 1562500000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312337194867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_22 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (41658073640271 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312341194783 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨22, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (41658073640271 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312341194783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_23 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83281567140161 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (92493807481 / 4000000000000 : ℝ))
      (E := (cell12244 ⟨23, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83281567140161 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (92493807481 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_24 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83247011376713 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156174587957 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨24, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83247011376713 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156174587957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_25 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (325048749833 / 390625000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312353165537 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨25, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (325048749833 / 390625000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312353165537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_26 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (16635594569797 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (115617857987 / 5000000000000 : ℝ))
      (E := (cell12244 ⟨26, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (16635594569797 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (115617857987 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_27 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (5196468126207 / 6250000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312361162137 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨27, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (5196468126207 / 6250000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312361162137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_28 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83109031435787 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578091279421 / 25000000000000 : ℝ))
      (E := (cell12244 ⟨28, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83109031435787 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578091279421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_29 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83074597066131 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156184573169 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨29, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83074597066131 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156184573169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_30 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (41520093439117 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312373134147 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨30, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (41520093439117 / 50000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312373134147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_31 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (83005800840147 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312377083719 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨31, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (83005800840147 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312377083719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_32 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (10371429865011 / 12500000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312381114453 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨32, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (10371429865011 / 12500000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312381114453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_33 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (16587420217287 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578096277891 / 25000000000000 : ℝ))
      (E := (cell12244 ⟨33, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (16587420217287 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (578096277891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_34 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82902787307729 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312389076969 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨34, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82902787307729 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312389076969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_35 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82868497552671 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156196535469 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨35, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82868497552671 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156196535469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_36 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82834231790121 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312397095001 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨36, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82834231790121 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312397095001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_37 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (827999899891 / 1000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312401091833 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨37, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (827999899891 / 1000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312401091833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_38 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (82765772118783 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156202531221 / 50000000000000 : ℝ))
      (E := (cell12244 ⟨38, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (82765772118783 / 100000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (1156202531221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12244_39 : CellCertificate 12244 (449942678737399 / 5000000000000000 : ℝ) (1715508486168073 / 1000000000000000000 : ℝ) (17342206963583 / 500000000000000 : ℝ)
    (cell12244 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · norm_num [cell12244]
  · have h := gap_lower (n := 12244) (a := (16546315629701 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312409066287 / 100000000000000 : ℝ))
      (E := (cell12244 ⟨39, by decide⟩).energy) (xi := (17342206963583 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12244 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12244]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12244])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12244) (a := (16546315629701 / 20000000000000 : ℝ)) (b := (168308294717 / 100000000000000 : ℝ)) (q := (2312409066287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12244])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12244]

theorem cert12245_20 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41692685615171 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312185451361 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨20, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41692685615171 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312185451361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_21 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (83350742565797 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (231218947297 / 10000000000000 : ℝ))
      (E := (cell12245 ⟨21, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (83350742565797 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (231218947297 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_22 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41658069172069 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156096712423 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨22, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41658069172069 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156096712423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_23 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (83281558532071 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156098714043 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨23, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (83281558532071 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156098714043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_24 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41623501548239 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156100714377 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨24, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41623501548239 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156100714377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_25 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (83212472004409 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289025678867 / 12500000000000 : ℝ))
      (E := (cell12245 ⟨25, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (83212472004409 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289025678867 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_26 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (16635593044617 / 20000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156104719239 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨26, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (16635593044617 / 20000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156104719239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_27 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (10392935339987 / 12500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312213396597 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨27, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (10392935339987 / 12500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312213396597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_28 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41554512231199 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312217425433 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨28, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41554512231199 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312217425433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_29 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20768647604579 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578055352829 / 25000000000000 : ℝ))
      (E := (cell12245 ⟨29, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20768647604579 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578055352829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_30 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (83040180555537 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462445071417 / 20000000000000 : ℝ))
      (E := (cell12245 ⟨30, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (83040180555537 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (462445071417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_31 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (83005794842117 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (28902867279 / 1250000000000 : ℝ))
      (E := (cell12245 ⟨31, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (83005794842117 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (28902867279 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_32 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (1296428644473 / 1562500000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578058343129 / 25000000000000 : ℝ))
      (E := (cell12245 ⟨32, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (1296428644473 / 1562500000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (578058343129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_33 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (82937095736383 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (46244747767 / 2000000000000 : ℝ))
      (E := (cell12245 ⟨33, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (82937095736383 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (46244747767 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_34 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (8290278228099 / 10000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312241373251 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨34, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (8290278228099 / 10000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312241373251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_35 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20717123212199 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289030666113 / 12500000000000 : ℝ))
      (E := (cell12245 ⟨35, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20717123212199 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (289030666113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_36 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (41417113704331 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156124686991 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨36, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (41417113704331 / 50000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156124686991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_37 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (10349998241201 / 12500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312253333969 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨37, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (10349998241201 / 12500000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312253333969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_38 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (20691442095203 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312257327109 / 100000000000000 : ℝ))
      (E := (cell12245 ⟨38, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (20691442095203 / 25000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (2312257327109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12245_39 : CellCertificate 12245 (899855387084573 / 10000000000000000 : ℝ) (1715368339701469 / 1000000000000000000 : ℝ) (13872602138011 / 400000000000000 : ℝ)
    (cell12245 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · norm_num [cell12245]
  · have h := gap_lower (n := 12245) (a := (82731574731609 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156130677127 / 50000000000000 : ℝ))
      (E := (cell12245 ⟨39, by decide⟩).energy) (xi := (13872602138011 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12245 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12245]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12245])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12245) (a := (82731574731609 / 100000000000000 : ℝ)) (b := (168294365147 / 100000000000000 : ℝ)) (q := (1156130677127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12245])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12245]

theorem cert12246_20 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (20846340409437 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (231203783197 / 10000000000000 : ℝ))
      (E := (cell12246 ⟨20, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (20846340409437 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (231203783197 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_21 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (20837683325599 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312041804871 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨21, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (20837683325599 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312041804871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_22 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83316129409469 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312045767053 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨22, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83316129409469 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312045767053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_23 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (3331261997027 / 4000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312049781379 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨23, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (3331261997027 / 4000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312049781379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_24 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (10405874352237 / 12500000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (578013448479 / 25000000000000 : ℝ))
      (E := (cell12246 ⟨24, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (10405874352237 / 12500000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (578013448479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_25 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41606232026591 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312057750399 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨25, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41606232026591 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312057750399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_26 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83177957598757 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462412354269 / 20000000000000 : ℝ))
      (E := (cell12246 ⟨26, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83177957598757 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (462412354269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_27 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (8314347542201 / 10000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156032871823 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨27, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (8314347542201 / 10000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156032871823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_28 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41554508745249 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (92482789161 / 4000000000000 : ℝ))
      (E := (cell12246 ⟨28, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41554508745249 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (92482789161 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_29 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (20768645942987 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312073730621 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨29, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (20768645942987 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312073730621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_30 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (10380021779281 / 12500000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144504859459 / 6250000000000 : ℝ))
      (E := (cell12246 ⟨30, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (10380021779281 / 12500000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144504859459 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_31 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (83005788845453 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312081735379 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨31, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (83005788845453 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312081735379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_32 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41485713786891 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312085743613 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨32, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41485713786891 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312085743613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_33 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (2591784074613 / 3125000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312089719723 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨33, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (2591784074613 / 3125000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312089719723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_34 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (16580555451099 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156046862093 / 50000000000000 : ℝ))
      (E := (cell12246 ⟨34, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (16580555451099 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (1156046862093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_35 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (20717122036531 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (578024425043 / 25000000000000 : ℝ))
      (E := (cell12246 ⟨35, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (20717122036531 / 25000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (578024425043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_36 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (16566844605673 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312101707747 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨36, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (16566844605673 / 20000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312101707747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_37 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41399990935619 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144506605599 / 6250000000000 : ℝ))
      (E := (cell12246 ⟨37, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41399990935619 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (144506605599 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_38 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (82765764643923 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312109705343 / 100000000000000 : ℝ))
      (E := (cell12246 ⟨38, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (82765764643923 / 100000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (2312109705343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12246_39 : CellCertificate 12246 (899825421411191 / 10000000000000000 : ℝ) (428807054032799 / 250000000000000000 : ℝ) (173392986316643 / 5000000000000000 : ℝ)
    (cell12246 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · norm_num [cell12246]
  · have h := gap_lower (n := 12246) (a := (41365785657877 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (5780284243 / 250000000000 : ℝ))
      (E := (cell12246 ⟨39, by decide⟩).energy) (xi := (173392986316643 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12246 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12246]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12246])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12246) (a := (41365785657877 / 50000000000000 : ℝ)) (b := (84140218957 / 50000000000000 : ℝ)) (q := (5780284243 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12246])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12246]

theorem cert12247_20 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (20846338011743 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462378053263 / 20000000000000 : ℝ))
      (E := (cell12247 ⟨20, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (20846338011743 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462378053263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_21 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (20837681010193 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577973562207 / 25000000000000 : ℝ))
      (E := (cell12247 ⟨21, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (20837681010193 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577973562207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_22 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (10414515059567 / 12500000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462379644281 / 20000000000000 : ℝ))
      (E := (cell12247 ⟨22, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (10414515059567 / 12500000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462379644281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_23 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (41640770660487 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311902246907 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨23, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (41640770660487 / 50000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311902246907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_24 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83246986540967 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311906213077 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨24, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83246986540967 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311906213077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_25 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83212456103567 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311910240623 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨25, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83212456103567 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311910240623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_26 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83177949975999 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462382843343 / 20000000000000 : ℝ))
      (E := (cell12247 ⟨26, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83177949975999 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462382843343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_27 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83143468125653 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (288989775411 / 12500000000000 : ℝ))
      (E := (cell12247 ⟨27, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83143468125653 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (288989775411 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_28 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83109010520087 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577980550929 / 25000000000000 : ℝ))
      (E := (cell12247 ⟨28, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83109010520087 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577980550929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_29 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (83074577127027 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311926162697 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨29, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (83074577127027 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311926162697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_30 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (16608033582873 / 20000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155965099999 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨30, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (16608033582873 / 20000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155965099999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_31 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (16601156570031 / 20000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311934201387 / 100000000000000 : ℝ))
      (E := (cell12247 ⟨31, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (16601156570031 / 20000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (2311934201387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_32 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (82971421902617 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577984542309 / 25000000000000 : ℝ))
      (E := (cell12247 ⟨32, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (82971421902617 / 100000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (577984542309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_33 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (20734271260033 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (92477686569 / 4000000000000 : ℝ))
      (E := (cell12247 ⟨33, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (20734271260033 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (92477686569 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_34 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (20725693057811 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (144496633111 / 6250000000000 : ℝ))
      (E := (cell12247 ⟨34, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (20725693057811 / 25000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (144496633111 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_35 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (5179280215291 / 6250000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (28899376577 / 1250000000000 : ℝ))
      (E := (cell12247 ⟨35, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (5179280215291 / 6250000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (28899376577 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_36 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (8283421864923 / 10000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462390830981 / 20000000000000 : ℝ))
      (E := (cell12247 ⟨36, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (8283421864923 / 10000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462390830981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_37 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (8279997781399 / 10000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155979079341 / 50000000000000 : ℝ))
      (E := (cell12247 ⟨37, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (8279997781399 / 10000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (1155979079341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_38 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (16553152181623 / 20000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462392427699 / 20000000000000 : ℝ))
      (E := (cell12247 ⟨38, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (16553152181623 / 20000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462392427699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12247_39 : CellCertificate 12247 (179959092090697 / 2000000000000000 : ℝ) (343017623090329 / 200000000000000000 : ℝ) (173378448409613 / 5000000000000000 : ℝ)
    (cell12247 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · norm_num [cell12247]
  · have h := gap_lower (n := 12247) (a := (4136578395047 / 5000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462393230761 / 20000000000000 : ℝ))
      (E := (cell12247 ⟨39, by decide⟩).energy) (xi := (173378448409613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12247 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12247]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12247])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12247) (a := (4136578395047 / 5000000000000 : ℝ)) (b := (21033314127 / 12500000000000 : ℝ)) (q := (462393230761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12247])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12247]

theorem cert12248_20 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83385342458013 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155871377199 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨20, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83385342458013 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155871377199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_21 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (3334028591237 / 4000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311746746587 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨21, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (3334028591237 / 4000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311746746587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_22 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83316111545339 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311750787903 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨22, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83316111545339 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311750787903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_23 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41640766358983 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (577938691593 / 25000000000000 : ℝ))
      (E := (cell12248 ⟨23, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41640766358983 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (577938691593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_24 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (8324697826569 / 10000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (462351748913 / 20000000000000 : ℝ))
      (E := (cell12248 ⟨24, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (8324697826569 / 10000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (462351748913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_25 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (20803112038891 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155881363283 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨25, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (20803112038891 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155881363283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_26 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83177942354811 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155883358109 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨26, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83177942354811 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155883358109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_27 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (3325738433233 / 4000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (288971339641 / 12500000000000 : ℝ))
      (E := (cell12248 ⟨27, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (3325738433233 / 4000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (288971339641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_28 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (83109003551163 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311774732673 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨28, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (83109003551163 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311774732673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_29 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41537285241777 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (462355741509 / 20000000000000 : ℝ))
      (E := (cell12248 ⟨29, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41537285241777 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (462355741509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_30 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (5190010099743 / 6250000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (288972837881 / 12500000000000 : ℝ))
      (E := (cell12248 ⟨30, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (5190010099743 / 6250000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (288972837881 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_31 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41502888428111 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (36121667529 / 1562500000000 : ℝ))
      (E := (cell12248 ⟨31, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41502888428111 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (36121667529 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_32 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (10371427029097 / 12500000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155895353949 / 50000000000000 : ℝ))
      (E := (cell12248 ⟨32, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (10371427029097 / 12500000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (1155895353949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_33 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82937079693933 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (577948665829 / 25000000000000 : ℝ))
      (E := (cell12248 ⟨33, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82937079693933 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (577948665829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_34 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (16580553441647 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (288974838393 / 12500000000000 : ℝ))
      (E := (cell12248 ⟨34, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (16580553441647 / 20000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (288974838393 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_35 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82868478744389 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (462360533091 / 20000000000000 : ℝ))
      (E := (cell12248 ⟨35, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82868478744389 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (462360533091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_36 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (41417107135629 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (46236133137 / 2000000000000 : ℝ))
      (E := (cell12248 ⟨36, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (41417107135629 / 50000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (46236133137 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_37 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (10349996719733 / 12500000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311810682631 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨37, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (10349996719733 / 12500000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311810682631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_38 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (20691439293347 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311814685219 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨38, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (20691439293347 / 25000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311814685219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12248_39 : CellCertificate 12248 (899765504210291 / 10000000000000000 : ℝ) (342989607531441 / 200000000000000000 : ℝ) (86681956501657 / 2500000000000000 : ℝ)
    (cell12248 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · norm_num [cell12248]
  · have h := gap_lower (n := 12248) (a := (82731564487167 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311818665393 / 100000000000000 : ℝ))
      (E := (cell12248 ⟨39, by decide⟩).energy) (xi := (86681956501657 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12248 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12248]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12248])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12248) (a := (82731564487167 / 100000000000000 : ℝ)) (b := (168252590453 / 100000000000000 : ℝ)) (q := (2311818665393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12248])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12248]

theorem cert12249_20 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83385332870873 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (57789885317 / 2500000000000 : ℝ))
      (E := (cell12249 ⟨20, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83385332870873 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (57789885317 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_21 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83350705522853 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155799707331 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨21, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83350705522853 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155799707331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_22 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (20829025653969 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311603408273 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨22, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (20829025653969 / 25000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311603408273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_23 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83281524116651 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155803699037 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨23, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83281524116651 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155803699037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_24 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (16649393998413 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311611388381 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨24, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (16649393998413 / 20000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311611388381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_25 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83212440209171 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155807691637 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨25, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83212440209171 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155807691637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_26 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83177934735193 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311619328227 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨26, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83177934735193 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311619328227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_27 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (3325738141501 / 4000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462324668713 / 20000000000000 : ℝ))
      (E := (cell12249 ⟨27, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (3325738141501 / 4000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462324668713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_28 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83108996583727 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462325463179 / 20000000000000 : ℝ))
      (E := (cell12249 ⟨28, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83108996583727 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (462325463179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_29 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (83074563841527 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (92465252269 / 4000000000000 : ℝ))
      (E := (cell12249 ⟨29, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (83074563841527 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (92465252269 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_30 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (2595004852463 / 3125000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155817659481 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨30, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (2595004852463 / 3125000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155817659481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_31 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41502885431827 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577909824197 / 25000000000000 : ℝ))
      (E := (cell12249 ⟨31, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41502885431827 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577909824197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_32 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82971410564259 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311643301089 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨32, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82971410564259 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311643301089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_33 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (10367134293627 / 12500000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577911833519 / 25000000000000 : ℝ))
      (E := (cell12249 ⟨33, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (10367134293627 / 12500000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577911833519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_34 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82902762186469 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311651280611 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨34, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82902762186469 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311651280611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_35 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (3314738961813 / 4000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311655318057 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨35, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (3314738961813 / 4000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311655318057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_36 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41417104947223 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311659272193 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨36, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41417104947223 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311659272193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_37 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41399984851429 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577915815359 / 25000000000000 : ℝ))
      (E := (cell12249 ⟨37, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41399984851429 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (577915815359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_38 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (82765753439741 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155833643431 / 50000000000000 : ℝ))
      (E := (cell12249 ⟨38, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (82765753439741 / 100000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (1155833643431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

theorem cert12249_39 : CellCertificate 12249 (899735552680443 / 10000000000000000 : ℝ) (6698468682587 / 3906250000000000 : ℝ) (346698760194027 / 10000000000000000 : ℝ)
    (cell12249 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · norm_num [cell12249]
  · have h := gap_lower (n := 12249) (a := (41365780537217 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311671290643 / 100000000000000 : ℝ))
      (E := (cell12249 ⟨39, by decide⟩).energy) (xi := (346698760194027 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12249 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12249]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12249])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12249) (a := (41365780537217 / 50000000000000 : ℝ)) (b := (10514916889 / 6250000000000 : ℝ)) (q := (2311671290643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12249])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12249]

end BstLean.Part263
