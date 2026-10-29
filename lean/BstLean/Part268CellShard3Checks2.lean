import BstLean.Part268CellShard3Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12425_40 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (82696863634313 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286913014231 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨40, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (82696863634313 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286913014231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_41 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (20665693669591 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286917008499 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨41, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (20665693669591 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286917008499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_42 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41314354726033 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286920994099 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨42, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41314354726033 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286920994099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_43 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (10324333490689 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (1143462485323 / 50000000000000 : ℝ))
      (E := (cell12425 ⟨43, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (10324333490689 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (1143462485323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_44 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (10320081258619 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286928996347 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨44, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (10320081258619 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286928996347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_45 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (82526655852781 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286933011613 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨45, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (82526655852781 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286933011613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_46 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41246342623773 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (114346847827 / 5000000000000 : ℝ))
      (E := (cell12425 ⟨46, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41246342623773 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (114346847827 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_47 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41229369111971 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571735251613 / 25000000000000 : ℝ))
      (E := (cell12425 ⟨47, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41229369111971 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571735251613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_48 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (20606203688203 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286944983291 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨48, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (20606203688203 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286944983291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_49 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (16478182961029 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286949003161 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨49, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (16478182961029 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286949003161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_50 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (3294281534083 / 4000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286953005271 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨50, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (3294281534083 / 4000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286953005271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_51 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (20580796341221 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (142934811719 / 6250000000000 : ℝ))
      (E := (cell12425 ⟨51, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (20580796341221 / 25000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (142934811719 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_52 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41144677907497 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228696100653 / 10000000000000 : ℝ))
      (E := (cell12425 ⟨52, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41144677907497 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (228696100653 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_53 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (3290221986959 / 4000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286965000851 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨53, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (3290221986959 / 4000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286965000851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_54 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (16444353382707 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (71467780241 / 3125000000000 : ℝ))
      (E := (cell12425 ⟨54, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (16444353382707 / 20000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (71467780241 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_55 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (41094003752763 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286972963221 / 100000000000000 : ℝ))
      (E := (cell12425 ⟨55, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (41094003752763 / 50000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (2286972963221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_56 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (82154271421941 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (1143488492137 / 50000000000000 : ℝ))
      (E := (cell12425 ⟨56, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (82154271421941 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (1143488492137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_57 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (82120558634913 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571745242109 / 25000000000000 : ℝ))
      (E := (cell12425 ⟨57, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (82120558634913 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (571745242109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_58 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (82086869116713 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (114349248563 / 5000000000000 : ℝ))
      (E := (cell12425 ⟨58, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (82086869116713 / 100000000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (114349248563 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12425_59 : CellCertificate 12425 (894536437477797 / 10000000000000000 : ℝ) (1690509581821039 / 1000000000000000000 : ℝ) (170829866771477 / 5000000000000000 : ℝ)
    (cell12425 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · norm_num [cell12425]
  · have h := gap_lower (n := 12425) (a := (10256650354969 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (457397797803 / 20000000000000 : ℝ))
      (E := (cell12425 ⟨59, by decide⟩).energy) (xi := (170829866771477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12425 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12425]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12425])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12425) (a := (10256650354969 / 12500000000000 : ℝ)) (b := (20728062679 / 12500000000000 : ℝ)) (q := (457397797803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12425])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12425]

theorem cert12426_40 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82696860714319 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143389064437 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨40, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82696860714319 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143389064437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_41 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41331386035701 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (285847762747 / 12500000000000 : ℝ))
      (E := (cell12426 ⟨41, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41331386035701 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (285847762747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_42 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82628707157701 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286786125887 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨42, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82628707157701 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286786125887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_43 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41297332971657 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286790082707 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨43, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41297332971657 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286790082707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_44 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (10320081049811 / 12500000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286794089391 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨44, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (10320081049811 / 12500000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286794089391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_45 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82526654493621 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (457359617269 / 20000000000000 : ℝ))
      (E := (cell12426 ⟨45, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82526654493621 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (457359617269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_46 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82492684199261 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143401036263 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨46, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82492684199261 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143401036263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_47 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41229368743051 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143403052781 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨47, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41229368743051 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143403052781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_48 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82424814324989 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (142925632821 / 6250000000000 : ℝ))
      (E := (cell12426 ⟨48, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82424814324989 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (142925632821 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_49 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (1287358041983 / 1562500000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286814129559 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨49, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (1287358041983 / 1562500000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286814129559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_50 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (16471407708601 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286818116927 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨50, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (16471407708601 / 20000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286818116927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_51 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (1646463717291 / 2000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286822085119 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨51, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (1646463717291 / 2000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286822085119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_52 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (20572339155743 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143413045403 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨52, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (20572339155743 / 25000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143413045403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_53 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82255550789839 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286830072489 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨53, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82255550789839 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286830072489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_54 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41110884168431 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143417043231 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨54, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41110884168431 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143417043231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_55 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82188009235893 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (228683812983 / 10000000000000 : ℝ))
      (E := (cell12426 ⟨55, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82188009235893 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (228683812983 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_56 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41077136729463 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286842081293 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨56, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41077136729463 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286842081293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_57 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (41060280489047 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286846114757 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨57, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (41060280489047 / 50000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286846114757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_58 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82086871765669 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286850108483 / 100000000000000 : ℝ))
      (E := (cell12426 ⟨58, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82086871765669 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (2286850108483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12426_59 : CellCertificate 12426 (111813412776699 / 1250000000000000 : ℝ) (1690373489944373 / 1000000000000000000 : ℝ) (341631530339913 / 10000000000000000 : ℝ)
    (cell12426 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · norm_num [cell12426]
  · have h := gap_lower (n := 12426) (a := (82053205794063 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143427058919 / 50000000000000 : ℝ))
      (E := (cell12426 ⟨59, by decide⟩).energy) (xi := (341631530339913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12426 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12426]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12426])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12426) (a := (82053205794063 / 100000000000000 : ℝ)) (b := (165810984741 / 100000000000000 : ℝ)) (q := (1143427058919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12426])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12426]

theorem cert12427_40 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82696857795273 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571660824699 / 25000000000000 : ℝ))
      (E := (cell12427 ⟨40, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82696857795273 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571660824699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_41 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (20665692366337 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457329450159 / 20000000000000 : ℝ))
      (E := (cell12427 ⟨41, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (20665692366337 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457329450159 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_42 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (41314352432103 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285831406789 / 12500000000000 : ℝ))
      (E := (cell12427 ⟨42, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (41314352432103 / 50000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285831406789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_43 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82594663961947 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286655250237 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨43, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82594663961947 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286655250237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_44 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82560646728817 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286659296779 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨44, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82560646728817 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286659296779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_45 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (5157915820951 / 6250000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571665818877 / 25000000000000 : ℝ))
      (E := (cell12427 ⟨45, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (5157915820951 / 6250000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571665818877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_46 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82492683151691 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285833412879 / 12500000000000 : ℝ))
      (E := (cell12427 ⟨46, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82492683151691 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285833412879 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_47 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (4122936837447 / 5000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (228667126039 / 10000000000000 : ℝ))
      (E := (cell12427 ⟨47, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (4122936837447 / 5000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (228667126039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_48 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (16484962779561 / 20000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (142917203991 / 6250000000000 : ℝ))
      (E := (cell12427 ⟨48, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (16484962779561 / 20000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (142917203991 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_49 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82390914569279 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285834906609 / 12500000000000 : ℝ))
      (E := (cell12427 ⟨49, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82390914569279 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (285834906609 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_50 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (2573657460453 / 3125000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571670821123 / 25000000000000 : ℝ))
      (E := (cell12427 ⟨50, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (2573657460453 / 3125000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571670821123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_51 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (4116159318237 / 5000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457337459537 / 20000000000000 : ℝ))
      (E := (cell12427 ⟨51, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (4116159318237 / 5000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (457337459537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_52 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (16457871486287 / 20000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (57167282253 / 2500000000000 : ℝ))
      (E := (cell12427 ⟨52, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (16457871486287 / 20000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (57167282253 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_53 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82255551906151 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (9146781037 / 400000000000 : ℝ))
      (E := (cell12427 ⟨53, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82255551906151 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (9146781037 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_54 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82221769760599 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286699261371 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨54, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82221769760599 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286699261371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_55 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (10273501370829 / 12500000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143351646793 / 50000000000000 : ℝ))
      (E := (cell12427 ⟨55, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (10273501370829 / 12500000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (1143351646793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_56 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (20538568874061 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286707293693 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨56, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (20538568874061 / 25000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286707293693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_57 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (8212056332157 / 10000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (35729863411 / 1562500000000 : ℝ))
      (E := (cell12427 ⟨57, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (8212056332157 / 10000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (35729863411 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_58 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82086874414883 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571678825529 / 25000000000000 : ℝ))
      (E := (cell12427 ⟨58, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82086874414883 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (571678825529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12427_59 : CellCertificate 12427 (894478171461381 / 10000000000000000 : ℝ) (1690237419977677 / 1000000000000000000 : ℝ) (85400832971921 / 2500000000000000 : ℝ)
    (cell12427 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · norm_num [cell12427]
  · have h := gap_lower (n := 12427) (a := (82053208748593 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286719303133 / 100000000000000 : ℝ))
      (E := (cell12427 ⟨59, by decide⟩).energy) (xi := (85400832971921 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12427 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12427]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12427])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12427) (a := (82053208748593 / 100000000000000 : ℝ)) (b := (41449367569 / 25000000000000 : ℝ)) (q := (2286719303133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12427])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12427]

theorem cert12428_40 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82696854877173 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286508523997 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨40, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82696854877173 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286508523997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_41 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82662766860201 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286512513701 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨41, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82662766860201 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286512513701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_42 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82628702571581 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286516496909 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨42, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82628702571581 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286516496909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_43 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (8259466198141 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143260266013 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨43, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (8259466198141 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143260266013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_44 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41280322529969 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457304900177 / 20000000000000 : ℝ))
      (E := (cell12428 ⟨44, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41280322529969 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457304900177 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_45 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (20631662944391 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143264260133 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨45, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (20631662944391 / 25000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143264260133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_46 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82492682104837 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286532530333 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨46, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82492682104837 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286532530333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_47 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41229368006227 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (91461461193 / 4000000000000 : ℝ))
      (E := (cell12428 ⟨47, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41229368006227 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (91461461193 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_48 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82424813471259 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286540517267 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨48, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82424813471259 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286540517267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_49 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41195457226123 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571636122741 / 25000000000000 : ℝ))
      (E := (cell12428 ⟨49, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41195457226123 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (571636122741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_50 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82357038926549 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286548507967 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨50, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82357038926549 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286548507967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_51 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (82323186865453 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457310501449 / 20000000000000 : ℝ))
      (E := (cell12428 ⟨51, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (82323186865453 / 100000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457310501449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_52 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (642885611253 / 781250000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (35727445101 / 1562500000000 : ℝ))
      (E := (cell12428 ⟨52, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (642885611253 / 781250000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (35727445101 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_53 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (8225555302291 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286560502109 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨53, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (8225555302291 / 10000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286560502109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_54 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (16444354236949 / 20000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (57164112311 / 2500000000000 : ℝ))
      (E := (cell12428 ⟨54, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (16444354236949 / 20000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (57164112311 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_55 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41094006348871 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457313702713 / 20000000000000 : ℝ))
      (E := (cell12428 ⟨55, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41094006348871 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (457313702713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_56 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (10269284691737 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (28582156291 / 1250000000000 : ℝ))
      (E := (cell12428 ⟨56, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (10269284691737 / 12500000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (28582156291 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_57 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41060282832671 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286576517319 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨57, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41060282832671 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286576517319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_58 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (41043438532177 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143290246507 / 50000000000000 : ℝ))
      (E := (cell12428 ⟨58, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (41043438532177 / 50000000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (1143290246507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12428_59 : CellCertificate 12428 (27951532663127 / 312500000000000 : ℝ) (845050685957829 / 500000000000000000 : ℝ) (341575138184931 / 10000000000000000 : ℝ)
    (cell12428 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · norm_num [cell12428]
  · have h := gap_lower (n := 12428) (a := (5128325731459 / 6250000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286584485731 / 100000000000000 : ℝ))
      (E := (cell12428 ⟨59, by decide⟩).energy) (xi := (341575138184931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12428 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12428]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12428])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12428) (a := (5128325731459 / 6250000000000 : ℝ)) (b := (165783958037 / 100000000000000 : ℝ)) (q := (2286584485731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12428])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12428]

theorem cert12429_40 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (4134842598001 / 5000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286373804477 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨40, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (4134842598001 / 5000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286373804477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_41 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82662764255963 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (571594443301 / 25000000000000 : ℝ))
      (E := (cell12429 ⟨41, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82662764255963 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (571594443301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_42 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (3305148011193 / 4000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286381794913 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨42, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (3305148011193 / 4000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286381794913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_43 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (10324332500213 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143192905247 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨43, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (10324332500213 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143192905247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_44 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82560643391851 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143194909669 / 50000000000000 : ℝ))
      (E := (cell12429 ⟨44, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82560643391851 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (1143194909669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_45 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (16505330084133 / 20000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (114319691031 / 5000000000000 : ℝ))
      (E := (cell12429 ⟨45, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (16505330084133 / 20000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (114319691031 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_46 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82492681058697 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286397813293 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨46, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82492681058697 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286397813293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_47 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20614683819161 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286401796097 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨47, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20614683819161 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286401796097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_48 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (10303101630669 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286405767553 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨48, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (10303101630669 / 12500000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286405767553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_49 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20597728583953 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286409784903 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨49, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20597728583953 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286409784903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_50 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20589259779791 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (45728275747 / 2000000000000 : ℝ))
      (E := (cell12429 ⟨50, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20589259779791 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (45728275747 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_51 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (8232318736669 / 10000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (285802221597 / 12500000000000 : ℝ))
      (E := (cell12429 ⟨51, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (8232318736669 / 10000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (285802221597 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_52 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82289359049817 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (285802724731 / 12500000000000 : ℝ))
      (E := (cell12429 ⟨52, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82289359049817 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (285802724731 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_53 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (20563888535029 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457285160213 / 20000000000000 : ℝ))
      (E := (cell12429 ⟨53, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (20563888535029 / 25000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457285160213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_54 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (822217726093 / 1000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (228642977967 / 10000000000000 : ℝ))
      (E := (cell12429 ⟨54, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (822217726093 / 1000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (228642977967 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_55 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82188014429223 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286433789767 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨55, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82188014429223 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286433789767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_56 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82154279571881 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (35725590143 / 1562500000000 : ℝ))
      (E := (cell12429 ⟨56, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82154279571881 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (35725590143 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_57 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82120568009409 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (57161044339 / 2500000000000 : ℝ))
      (E := (cell12429 ⟨57, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82120568009409 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (57161044339 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_58 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (82086879714083 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457289159893 / 20000000000000 : ℝ))
      (E := (cell12429 ⟨58, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (82086879714083 / 100000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (457289159893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12429_59 : CellCertificate 12429 (27950622609017 / 312500000000000 : ℝ) (1689965345753029 / 1000000000000000000 : ℝ) (85386737307579 / 2500000000000000 : ℝ)
    (cell12429 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · norm_num [cell12429]
  · have h := gap_lower (n := 12429) (a := (41026607329157 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286449783969 / 100000000000000 : ℝ))
      (E := (cell12429 ⟨59, by decide⟩).energy) (xi := (85386737307579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12429 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12429]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12429])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12429) (a := (41026607329157 / 50000000000000 : ℝ)) (b := (20721306003 / 12500000000000 : ℝ)) (q := (2286449783969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12429])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12429]

theorem cert12430_40 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82696849043813 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (28577989253 / 1250000000000 : ℝ))
      (E := (cell12430 ⟨40, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82696849043813 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (28577989253 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_41 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82662761652633 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286243146797 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨41, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82662761652633 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286243146797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_42 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41314348994469 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (91449885933 / 4000000000000 : ℝ))
      (E := (cell12430 ⟨42, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41314348994469 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (91449885933 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_43 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82594658022829 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (142890696527 / 6250000000000 : ℝ))
      (E := (cell12430 ⟨43, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82594658022829 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (142890696527 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_44 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (20640160431139 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286255134511 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨44, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (20640160431139 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286255134511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_45 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (2063166226613 / 2500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286259117733 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨45, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (2063166226613 / 2500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286259117733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_46 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (10311585001659 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143131575957 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨46, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (10311585001659 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143131575957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_47 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82458734541511 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571566779523 / 25000000000000 : ℝ))
      (E := (cell12430 ⟨47, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82458734541511 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (571566779523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_48 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (41212406310041 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (285783891567 / 12500000000000 : ℝ))
      (E := (cell12430 ⟨48, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (41212406310041 / 50000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (285783891567 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_49 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82390914219979 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (228627513469 / 10000000000000 : ℝ))
      (E := (cell12430 ⟨49, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82390914219979 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (228627513469 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_50 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (4117851965617 / 5000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143139561323 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨50, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (4117851965617 / 5000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143139561323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_51 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (1646463757369 / 2000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286283153261 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨51, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (1646463757369 / 2000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286283153261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_52 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (10286169982467 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286287165269 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨52, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (10286169982467 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286287165269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_53 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82255555257769 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143145578061 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨53, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82255555257769 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143145578061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_54 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (10277721754283 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286295123061 / 100000000000000 : ℝ))
      (E := (cell12430 ⟨54, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (10277721754283 / 12500000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (2286295123061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_55 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (3287520646443 / 4000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143149561097 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨55, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (3287520646443 / 4000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143149561097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_56 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82154281610199 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (228630315041 / 10000000000000 : ℝ))
      (E := (cell12430 ⟨56, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82154281610199 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (228630315041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_57 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (20530142588443 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (285788393159 / 12500000000000 : ℝ))
      (E := (cell12430 ⟨57, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (20530142588443 / 25000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (285788393159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_58 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (82086882364069 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (228631116233 / 10000000000000 : ℝ))
      (E := (cell12430 ⟨58, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (82086882364069 / 100000000000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (228631116233 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12430_59 : CellCertificate 12430 (894390806265723 / 10000000000000000 : ℝ) (844914670742251 / 500000000000000000 : ℝ) (341518765022503 / 10000000000000000 : ℝ)
    (cell12430 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · norm_num [cell12430]
  · have h := gap_lower (n := 12430) (a := (1282081525211 / 1562500000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143157569341 / 50000000000000 : ℝ))
      (E := (cell12430 ⟨59, by decide⟩).energy) (xi := (341518765022503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12430 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12430]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12430])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12430) (a := (1282081525211 / 1562500000000 : ℝ)) (b := (33151388047 / 20000000000000 : ℝ)) (q := (1143157569341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12430])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12430]

theorem cert12431_40 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82696846128553 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286104531283 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨40, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82696846128553 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286104531283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_41 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (8266275905021 / 10000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286108516991 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨41, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (8266275905021 / 10000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286108516991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_42 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (2065717392473 / 2500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (285764069643 / 12500000000000 : ℝ))
      (E := (cell12431 ⟨42, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (2065717392473 / 2500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (285764069643 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_43 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82594656044783 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286116533843 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨43, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82594656044783 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286116533843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_44 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (20640160014513 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286120564033 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨44, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (20640160014513 / 25000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286120564033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_45 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (10315830963641 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286124529281 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨45, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (10315830963641 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286124529281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_46 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (41246339484281 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457225709239 / 20000000000000 : ℝ))
      (E := (cell12431 ⟨46, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (41246339484281 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457225709239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_47 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82458733807053 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (285766569337 / 12500000000000 : ℝ))
      (E := (cell12431 ⟨47, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82458733807053 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (285766569337 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_48 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (1648496243909 / 2000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (285767069163 / 12500000000000 : ℝ))
      (E := (cell12431 ⟨48, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (1648496243909 / 2000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (285767069163 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_49 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (16478182820949 / 20000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1143070270163 / 50000000000000 : ℝ))
      (E := (cell12431 ⟨49, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (16478182820949 / 20000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1143070270163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_50 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82357039506077 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1143072256927 / 50000000000000 : ℝ))
      (E := (cell12431 ⟨50, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82357039506077 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (1143072256927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_51 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82323188370733 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286148530741 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨51, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82323188370733 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286148530741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_52 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82289360670139 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571538132431 / 25000000000000 : ℝ))
      (E := (cell12431 ⟨52, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82289360670139 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (571538132431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_53 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82255556375869 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286156508251 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨53, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82255556375869 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286156508251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_54 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82221775459637 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457232104523 / 20000000000000 : ℝ))
      (E := (cell12431 ⟨54, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82221775459637 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457232104523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_55 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (41094008946649 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457232902169 / 20000000000000 : ℝ))
      (E := (cell12431 ⟨55, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (41094008946649 / 50000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (457232902169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_56 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (1643085672977 / 2000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286168528857 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨56, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (1643085672977 / 2000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286168528857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_57 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82120572698429 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286172514213 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨57, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82120572698429 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286172514213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_58 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (10260860626789 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286176522461 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨58, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (10260860626789 / 12500000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286176522461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12431_59 : CellCertificate 12431 (447180846775253 / 5000000000000000 : ℝ) (211211669888099 / 125000000000000000 : ℝ) (170745292780079 / 5000000000000000 : ℝ)
    (cell12431 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · norm_num [cell12431]
  · have h := gap_lower (n := 12431) (a := (82053220568913 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286180549869 / 100000000000000 : ℝ))
      (E := (cell12431 ⟨59, by decide⟩).energy) (xi := (170745292780079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12431 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12431]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12431])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12431) (a := (82053220568913 / 100000000000000 : ℝ)) (b := (165743434671 / 100000000000000 : ℝ)) (q := (2286180549869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12431])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12431]

theorem cert12432_40 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41348421607119 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285969977611 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨40, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41348421607119 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285969977611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_41 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41331378224347 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571493500319 / 25000000000000 : ℝ))
      (E := (cell12432 ⟨41, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41331378224347 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571493500319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_42 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (8262869340977 / 10000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (18287824171 / 800000000000 : ℝ))
      (E := (cell12432 ⟨42, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (8262869340977 / 10000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (18287824171 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_43 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82594654067567 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285981978727 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨43, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82594654067567 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285981978727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_44 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82560638392339 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285985990277 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨44, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82560638392339 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285985990277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_45 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (10315830794311 / 12500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (228598999643 / 10000000000000 : ℝ))
      (E := (cell12432 ⟨45, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (10315830794311 / 12500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (228598999643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_46 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (16498535584913 / 20000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285993996139 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨46, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (16498535584913 / 20000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2285993996139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_47 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (10307341634159 / 12500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (114299899407 / 5000000000000 : ℝ))
      (E := (cell12432 ⟨47, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (10307341634159 / 12500000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (114299899407 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_48 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (16484962354291 / 20000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286001970953 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨48, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (16484962354291 / 20000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286001970953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_49 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82390913990109 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (457201200363 / 20000000000000 : ℝ))
      (E := (cell12432 ⟨49, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82390913990109 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (457201200363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_50 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (658856317603 / 800000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571502504983 / 25000000000000 : ℝ))
      (E := (cell12432 ⟨50, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (658856317603 / 800000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (571502504983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_51 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41161594436769 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286014023179 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨51, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41161594436769 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286014023179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_52 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (20572340370257 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (114300900461 / 5000000000000 : ℝ))
      (E := (cell12432 ⟨52, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (20572340370257 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (114300900461 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_53 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (5140972343401 / 6250000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286021975509 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨53, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (5140972343401 / 6250000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286021975509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_54 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41110888442709 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (457205195667 / 20000000000000 : ℝ))
      (E := (cell12432 ⟨54, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41110888442709 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (457205195667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_55 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82188019625891 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1143015007399 / 50000000000000 : ℝ))
      (E := (cell12432 ⟨55, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82188019625891 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (1143015007399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_56 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82154285687833 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286034022691 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨56, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82154285687833 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286034022691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_57 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (82120575043381 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286037998627 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨57, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (82120575043381 / 100000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286037998627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_58 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (20521721916203 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (285755249769 / 12500000000000 : ℝ))
      (E := (cell12432 ⟨58, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (20521721916203 / 25000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (285755249769 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12432_59 : CellCertificate 12432 (178866517068359 / 2000000000000000 : ℝ) (337911479721723 / 200000000000000000 : ℝ) (68292482168389 / 2000000000000000 : ℝ)
    (cell12432 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · norm_num [cell12432]
  · have h := gap_lower (n := 12432) (a := (41026611762271 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286046017531 / 100000000000000 : ℝ))
      (E := (cell12432 ⟨59, by decide⟩).energy) (xi := (68292482168389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12432 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12432]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12432])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12432) (a := (41026611762271 / 50000000000000 : ℝ)) (b := (16572993133 / 10000000000000 : ℝ)) (q := (2286046017531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12432])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12432]

theorem cert12433_40 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82696840300869 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (285729442243 / 12500000000000 : ℝ))
      (E := (cell12433 ⟨40, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82696840300869 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (285729442243 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_41 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (20665688462021 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457167896433 / 20000000000000 : ℝ))
      (E := (cell12433 ⟨41, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (20665688462021 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457167896433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_42 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (5164293195093 / 6250000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285843482249 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨42, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (5164293195093 / 6250000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285843482249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_43 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82594652091181 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (18286780303 / 800000000000 : ℝ))
      (E := (cell12433 ⟨43, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82594652091181 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (18286780303 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_44 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82560636727417 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285851530873 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨44, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82560636727417 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285851530873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_45 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82526645000601 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142927759589 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨45, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82526645000601 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142927759589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_46 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82492676881283 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142929750873 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨46, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82492676881283 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142929750873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_47 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41229366170083 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457172707239 / 20000000000000 : ℝ))
      (E := (cell12433 ⟨47, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41229366170083 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457172707239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_48 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82424811348097 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285867503299 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨48, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82424811348097 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285867503299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_49 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82390913876073 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457174303831 / 20000000000000 : ℝ))
      (E := (cell12433 ⟨49, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82390913876073 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (457174303831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_50 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41178519947617 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (285734440371 / 12500000000000 : ℝ))
      (E := (cell12433 ⟨50, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41178519947617 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (285734440371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_51 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (41161594688433 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285879512613 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨51, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (41161594688433 / 50000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285879512613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_52 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (205723405731 / 250000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142941742877 / 50000000000000 : ℝ))
      (E := (cell12433 ⟨52, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (205723405731 / 250000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (1142941742877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_53 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82255558613409 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285887498869 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨53, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82255558613409 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285887498869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_54 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (10277722288951 / 12500000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285891490217 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨54, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (10277722288951 / 12500000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285891490217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_55 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (16437604271771 / 20000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285895515903 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨55, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (16437604271771 / 20000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285895515903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_56 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82154287727149 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285899513717 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨56, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82154287727149 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285899513717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_57 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (20530144347157 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (35717242803 / 1562500000000 : ℝ))
      (E := (cell12433 ⟨57, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (20530144347157 / 25000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (35717242803 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_58 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82086890315569 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (142869220641 / 6250000000000 : ℝ))
      (E := (cell12433 ⟨58, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82086890315569 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (142869220641 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12433_59 : CellCertificate 12433 (447151740819247 / 5000000000000000 : ℝ) (52794420624709 / 31250000000000000 : ℝ) (34143424086653 / 1000000000000000 : ℝ)
    (cell12433 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · norm_num [cell12433]
  · have h := gap_lower (n := 12433) (a := (82053226480389 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285911541671 / 100000000000000 : ℝ))
      (E := (cell12433 ⟨59, by decide⟩).energy) (xi := (34143424086653 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12433 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12433]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12433])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12433) (a := (82053226480389 / 100000000000000 : ℝ)) (b := (165716430213 / 100000000000000 : ℝ)) (q := (2285911541671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12433])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12433]

theorem cert12434_40 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (16539367477689 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142850547421 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨40, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (16539367477689 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142850547421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_41 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82662751248381 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571426269287 / 25000000000000 : ℝ))
      (E := (cell12434 ⟨41, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82662751248381 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571426269287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_42 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82628688834073 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (285713632163 / 12500000000000 : ℝ))
      (E := (cell12434 ⟨42, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82628688834073 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (285713632163 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_43 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (10324331264453 / 12500000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285713093709 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨43, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (10324331264453 / 12500000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285713093709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_44 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41280317531643 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (71428658381 / 3125000000000 : ℝ))
      (E := (cell12434 ⟨44, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41280317531643 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (71428658381 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_45 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (16505328729493 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285721097529 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨45, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (16505328729493 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285721097529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_46 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41246337919357 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142862531509 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨46, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41246337919357 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142862531509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_47 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (16491746321547 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285729081093 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨47, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (16491746321547 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285729081093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_48 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82424810925377 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (457146618287 / 20000000000000 : ℝ))
      (E := (cell12434 ⟨48, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82424810925377 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (457146618287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_49 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (20597728440659 / 25000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285737092347 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨49, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (20597728440659 / 25000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285737092347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_50 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (41178520045327 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285741081919 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨50, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (41178520045327 / 50000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285741081919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_51 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82323189880717 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142872529013 / 50000000000000 : ℝ))
      (E := (cell12434 ⟨51, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82323189880717 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (1142872529013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_52 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82289363104257 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571437269333 / 25000000000000 : ℝ))
      (E := (cell12434 ⟨52, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82289363104257 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571437269333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_53 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (5140972483303 / 6250000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285753078333 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨53, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (5140972483303 / 6250000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285753078333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_54 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (16444355947641 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571439264567 / 25000000000000 : ℝ))
      (E := (cell12434 ⟨54, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (16444355947641 / 20000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (571439264567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_55 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82188023092189 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285761073237 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨55, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82188023092189 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285761073237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_56 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82154289766797 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (457153012207 / 20000000000000 : ℝ))
      (E := (cell12434 ⟨56, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82154289766797 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (457153012207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_57 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82120579734169 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (228576907739 / 10000000000000 : ℝ))
      (E := (cell12434 ⟨57, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82120579734169 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (228576907739 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_58 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (82086892966583 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (142860816227 / 6250000000000 : ℝ))
      (E := (cell12434 ⟨58, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (82086892966583 / 100000000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (142860816227 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12434_59 : CellCertificate 12434 (223568595609877 / 2500000000000000 : ℝ) (422321385811433 / 250000000000000000 : ℝ) (17070303781629 / 500000000000000 : ℝ)
    (cell12434 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · norm_num [cell12434]
  · have h := gap_lower (n := 12434) (a := (10256653679557 / 12500000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285777063121 / 100000000000000 : ℝ))
      (E := (cell12434 ⟨59, by decide⟩).energy) (xi := (17070303781629 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12434 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12434]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12434])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12434) (a := (10256653679557 / 12500000000000 : ℝ)) (b := (82851465659 / 50000000000000 : ℝ)) (q := (2285777063121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12434])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12434]

theorem cert12435_40 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41348417238483 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285566707029 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨40, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41348417238483 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285566707029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_41 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (16532549729917 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285570727481 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨41, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (16532549729917 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285570727481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_42 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82628686547527 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571393671943 / 25000000000000 : ℝ))
      (E := (cell12435 ⟨42, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82628686547527 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571393671943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_43 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (2581082754403 / 3125000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285578705019 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨43, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (2581082754403 / 3125000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285578705019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_44 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41280316699973 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285582719867 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨44, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41280316699973 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285582719867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_45 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41263321147541 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285586731483 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨45, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41263321147541 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285586731483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_46 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82492674796859 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571397669989 / 25000000000000 : ℝ))
      (E := (cell12435 ⟨46, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82492674796859 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (571397669989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_47 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (4122936543799 / 5000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285594681719 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨47, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (4122936543799 / 5000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285594681719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_48 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82424810503293 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457119735291 / 20000000000000 : ℝ))
      (E := (cell12435 ⟨48, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82424810503293 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457119735291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_49 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82390913649797 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457120544279 / 20000000000000 : ℝ))
      (E := (cell12435 ⟨49, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82390913649797 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457120544279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_50 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82357040286633 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285606696789 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨50, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82357040286633 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285606696789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_51 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82323190385089 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285610718399 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨51, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82323190385089 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285610718399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_52 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41144681958299 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285614724953 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨52, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41144681958299 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285614724953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_53 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (20563890213183 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285618713903 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨53, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (20563890213183 / 25000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285618713903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_54 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82221781165211 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457124536497 / 20000000000000 : ℝ))
      (E := (cell12435 ⟨54, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82221781165211 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (457124536497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_55 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (82188024825893 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142813343401 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨55, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (82188024825893 / 100000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142813343401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_56 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41077145903389 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142815361871 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨56, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41077145903389 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142815361871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_57 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (16424116416001 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (142852170679 / 6250000000000 : ℝ))
      (E := (cell12435 ⟨57, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (16424116416001 / 20000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (142852170679 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_58 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41043447808927 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285638704569 / 100000000000000 : ℝ))
      (E := (cell12435 ⟨58, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41043447808927 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (2285638704569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12435_59 : CellCertificate 12435 (894245287743741 / 10000000000000000 : ℝ) (1689149648368467 / 1000000000000000000 : ℝ) (341377915138763 / 10000000000000000 : ℝ)
    (cell12435 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · norm_num [cell12435]
  · have h := gap_lower (n := 12435) (a := (41026616196371 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142821350109 / 50000000000000 : ℝ))
      (E := (cell12435 ⟨59, by decide⟩).energy) (xi := (341377915138763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12435 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12435]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12435])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12435) (a := (41026616196371 / 50000000000000 : ℝ)) (b := (41422358661 / 25000000000000 : ℝ)) (q := (1142821350109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12435])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12435]

theorem cert12436_40 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (2584275986451 / 3125000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285432374501 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨40, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (2584275986451 / 3125000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285432374501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_41 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41331373025847 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285436374421 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨41, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41331373025847 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285436374421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_42 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (10328585532731 / 12500000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285440373653 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨42, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (10328585532731 / 12500000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285440373653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_43 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (20648661541749 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285444371807 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨43, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (20648661541749 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285444371807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_44 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (16512126347479 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285448368267 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨44, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (16512126347479 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285448368267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_45 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82526640943451 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (11427261811 / 500000000000 : ℝ))
      (E := (cell12436 ⟨45, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82526640943451 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (11427261811 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_46 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82492673755717 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285456411421 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨46, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82492673755717 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285456411421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_47 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82458730144899 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (14284127481 / 625000000000 : ℝ))
      (E := (cell12436 ⟨47, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82458730144899 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (14284127481 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_48 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41212405040923 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142732188087 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨48, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41212405040923 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142732188087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_49 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (20597728384389 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142734203149 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨49, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (20597728384389 / 25000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142734203149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_50 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82357040483173 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (91418894703 / 4000000000000 : ℝ))
      (E := (cell12436 ⟨50, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82357040483173 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (91418894703 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_51 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (160787482207 / 195312500000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285476375771 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨51, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (160787482207 / 195312500000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285476375771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_52 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41144682364711 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285480369613 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨52, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41144682364711 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285480369613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_53 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82255561973063 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285484405577 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨53, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82255561973063 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285484405577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_54 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (657774260741 / 800000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285488362869 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨54, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (657774260741 / 800000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285488362869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_55 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82188026559967 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (228549241567 / 10000000000000 : ℝ))
      (E := (cell12436 ⟨55, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82188026559967 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (228549241567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_56 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (8215429384709 / 10000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (571374095911 / 25000000000000 : ℝ))
      (E := (cell12436 ⟨56, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (8215429384709 / 10000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (571374095911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_57 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (16424116885227 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285500381571 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨57, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (16424116885227 / 20000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285500381571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_58 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (82086898269381 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285504405923 / 100000000000000 : ℝ))
      (E := (cell12436 ⟨58, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (82086898269381 / 100000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (2285504405923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12436_59 : CellCertificate 12436 (447108098775049 / 5000000000000000 : ℝ) (1689013775353617 / 1000000000000000000 : ℝ) (68269951876749 / 2000000000000000 : ℝ)
    (cell12436 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · norm_num [cell12436]
  · have h := gap_lower (n := 12436) (a := (41026617674623 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142754196897 / 50000000000000 : ℝ))
      (E := (cell12436 ⟨59, by decide⟩).energy) (xi := (68269951876749 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12436 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12436]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12436])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12436) (a := (41026617674623 / 50000000000000 : ℝ)) (b := (165675940193 / 100000000000000 : ℝ)) (q := (1142754196897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12436])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12436]

theorem cert12437_40 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41348414328421 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142649077993 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨40, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41348414328421 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142649077993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_41 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (82662743454709 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142651067729 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨41, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (82662743454709 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142651067729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_42 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (16525736395407 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285663264369 / 12500000000000 : ℝ))
      (E := (cell12437 ⟨42, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (16525736395407 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285663264369 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_43 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (3303785767757 / 4000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142655076433 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨43, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (3303785767757 / 4000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142655076433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_44 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (16512126015127 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285314131023 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨44, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (16512126015127 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285314131023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_45 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (8252663959257 / 10000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285318107363 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨45, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (8252663959257 / 10000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285318107363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_46 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (82492672715289 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285322139693 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨46, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (82492672715289 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285322139693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_47 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (82458729414493 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142663054523 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨47, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (82458729414493 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142663054523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_48 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (16484961932207 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285666266461 / 12500000000000 : ℝ))
      (E := (cell12437 ⟨48, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (16484961932207 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (285666266461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_49 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41195456712957 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (142833384191 / 6250000000000 : ℝ))
      (E := (cell12437 ⟨49, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41195456712957 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (142833384191 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_50 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (5147315042517 / 6250000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142669076619 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨50, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (5147315042517 / 6250000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142669076619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_51 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (411615956977 / 500000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285342148107 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨51, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (411615956977 / 500000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285342148107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_52 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (82289365542731 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285346129321 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨52, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (82289365542731 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285346129321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_53 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (1028194538673 / 1250000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142675076679 / 50000000000000 : ℝ))
      (E := (cell12437 ⟨53, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (1028194538673 / 1250000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (1142675076679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_54 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (41110892010223 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (71417315607 / 3125000000000 : ℝ))
      (E := (cell12437 ⟨54, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (41110892010223 / 50000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (71417315607 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_55 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (82188028294411 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285358141697 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨55, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (82188028294411 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285358141697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_56 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (16430859177547 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (3570878281 / 156250000000 : ℝ))
      (E := (cell12437 ⟨56, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (16430859177547 / 20000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (3570878281 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_57 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (82120586772559 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285366147757 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨57, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (82120586772559 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285366147757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_58 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (20521725230291 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285370104551 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨58, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (20521725230291 / 25000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285370104551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12437_59 : CellCertificate 12437 (223546777964371 / 2500000000000000 : ℝ) (337775584839181 / 200000000000000000 : ℝ) (85330402091549 / 2500000000000000 : ℝ)
    (cell12437 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · norm_num [cell12437]
  · have h := gap_lower (n := 12437) (a := (82053238305969 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285374143851 / 100000000000000 : ℝ))
      (E := (cell12437 ⟨59, by decide⟩).energy) (xi := (85330402091549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12437 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12437]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12437])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12437) (a := (82053238305969 / 100000000000000 : ℝ)) (b := (82831223981 / 50000000000000 : ℝ)) (q := (2285374143851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12437])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12437]

theorem cert12438_40 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20674206437049 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (57129098351 / 2500000000000 : ℝ))
      (E := (cell12438 ⟨40, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20674206437049 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (57129098351 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_41 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (8266274085863 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (142822993319 / 6250000000000 : ℝ))
      (E := (cell12438 ⟨41, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (8266274085863 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (142822993319 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_42 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (8262867969309 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285171911667 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨42, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (8262867969309 / 10000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285171911667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_43 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41297321110841 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285175930613 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨43, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41297321110841 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285175930613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_44 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (10320078551833 / 12500000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285179890509 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨44, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (10320078551833 / 12500000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285179890509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_45 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41263319121221 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (228518390813 / 10000000000000 : ℝ))
      (E := (cell12438 ⟨45, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41263319121221 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (228518390813 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_46 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20623167918893 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457037584727 / 20000000000000 : ℝ))
      (E := (cell12438 ⟨46, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20623167918893 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457037584727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_47 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82458728684761 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285191935751 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨47, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82458728684761 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285191935751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_48 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (4121240462043 / 5000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142597971499 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨48, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (4121240462043 / 5000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142597971499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_49 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82390913314869 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285199943673 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨49, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82390913314869 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285199943673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_50 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82357040877931 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457040787173 / 20000000000000 : ℝ))
      (E := (cell12438 ⟨50, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82357040877931 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (457040787173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_51 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41161595950669 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (571301979361 / 25000000000000 : ℝ))
      (E := (cell12438 ⟨51, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41161595950669 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (571301979361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_52 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (41144683178261 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (91408477803 / 4000000000000 : ℝ))
      (E := (cell12438 ⟨52, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (41144683178261 / 50000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (91408477803 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_53 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82255564215061 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142607949111 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨53, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82255564215061 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142607949111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_54 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (3288871417947 / 4000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285219892149 / 100000000000000 : ℝ))
      (E := (cell12438 ⟨54, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (3288871417947 / 4000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (2285219892149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_55 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (10273503753653 / 12500000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (571305980989 / 25000000000000 : ℝ))
      (E := (cell12438 ⟨55, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (10273503753653 / 12500000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (571305980989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_56 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82154297928711 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (228522793143 / 10000000000000 : ℝ))
      (E := (cell12438 ⟨56, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82154297928711 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (228522793143 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_57 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82120589119277 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142615955589 / 50000000000000 : ℝ))
      (E := (cell12438 ⟨57, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82120589119277 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (1142615955589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_58 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (20521725893301 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (285654489843 / 12500000000000 : ℝ))
      (E := (cell12438 ⟨58, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (20521725893301 / 25000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (285654489843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12438_59 : CellCertificate 12438 (178831606132961 / 2000000000000000 : ℝ) (84437104744503 / 50000000000000000 : ℝ) (170646731042393 / 5000000000000000 : ℝ)
    (cell12438 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · norm_num [cell12438]
  · have h := gap_lower (n := 12438) (a := (82053241262911 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (228523995039 / 10000000000000 : ℝ))
      (E := (cell12438 ⟨59, by decide⟩).energy) (xi := (170646731042393 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12438 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12438]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12438])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12438) (a := (82053241262911 / 100000000000000 : ℝ)) (b := (165648957951 / 100000000000000 : ℝ)) (q := (228523995039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12438])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12438]

theorem cert12439_40 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41348411420247 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142514883693 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨40, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41348411420247 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142514883693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_41 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (2583210570733 / 3125000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (45700675297 / 2000000000000 : ℝ))
      (E := (cell12439 ⟨41, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (2583210570733 / 3125000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (45700675297 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_42 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82628677410011 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285037763801 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨42, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82628677410011 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285037763801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_43 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82594640250267 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285041763841 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨43, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82594640250267 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285041763841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_44 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41280313377241 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142522882177 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨44, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41280313377241 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142522882177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_45 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82526636893063 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285049764507 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨45, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82526636893063 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285049764507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_46 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82492670636569 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (457010752649 / 20000000000000 : ℝ))
      (E := (cell12439 ⟨46, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82492670636569 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (457010752649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_47 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (10307340994463 / 12500000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142528879651 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨47, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (10307340994463 / 12500000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142528879651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_48 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41212404410661 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (285632718899 / 12500000000000 : ℝ))
      (E := (cell12439 ⟨48, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41212404410661 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (285632718899 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_49 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (41195456602211 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571266449037 / 25000000000000 : ℝ))
      (E := (cell12439 ⟨49, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (41195456602211 / 50000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571266449037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_50 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (1647140821523 / 2000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571267443603 / 25000000000000 : ℝ))
      (E := (cell12439 ⟨50, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (1647140821523 / 2000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (571267443603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_51 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82323192407797 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (457014748553 / 20000000000000 : ℝ))
      (E := (cell12439 ⟨51, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82323192407797 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (457014748553 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_52 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82289367170797 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285077757871 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨52, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82289367170797 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285077757871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_53 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82255565336729 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285081758219 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨53, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82255565336729 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285081758219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_54 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82221786877311 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142542870523 / 50000000000000 : ℝ))
      (E := (cell12439 ⟨54, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82221786877311 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (1142542870523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_55 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82188031764407 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285089762449 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨55, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82188031764407 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285089762449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_56 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82154299970019 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285093760217 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨56, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82154299970019 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285093760217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_57 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82120591466289 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285097790079 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨57, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82120591466289 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285097790079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_58 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (164173812451 / 200000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285101789357 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨58, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (164173812451 / 200000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285101789357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12439_59 : CellCertificate 12439 (894128953970967 / 10000000000000000 : ℝ) (211075785928851 / 125000000000000000 : ℝ) (341265320538183 / 10000000000000000 : ℝ)
    (cell12439 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · norm_num [cell12439]
  · have h := gap_lower (n := 12439) (a := (82053244220071 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285105754243 / 100000000000000 : ℝ))
      (E := (cell12439 ⟨59, by decide⟩).energy) (xi := (341265320538183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12439 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12439]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12439])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12439) (a := (82053244220071 / 100000000000000 : ℝ)) (b := (2070443377 / 1250000000000 : ℝ)) (q := (2285105754243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12439])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12439]

theorem cert12440_40 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (16539363986747 / 20000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (91395826241 / 4000000000000 : ℝ))
      (E := (cell12440 ⟨40, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (16539363986747 / 20000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (91395826241 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_41 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41331367834593 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284899691953 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨41, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41331367834593 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284899691953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_42 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41314337563899 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142451835677 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨42, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41314337563899 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142451835677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_43 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (16131765289 / 19531250000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284907652551 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨43, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (16131765289 / 19531250000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284907652551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_44 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (8256062509509 / 10000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (142806980859 / 6250000000000 : ℝ))
      (E := (cell12440 ⟨44, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (8256062509509 / 10000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (142806980859 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_45 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (20631658886109 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (228491567649 / 10000000000000 : ℝ))
      (E := (cell12440 ⟨45, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (20631658886109 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (228491567649 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_46 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41246334799139 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284919658527 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨46, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41246334799139 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284919658527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_47 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (2061468180683 / 2500000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142461848737 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨47, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (2061468180683 / 2500000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142461848737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_48 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41212404201209 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142463837047 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨48, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41212404201209 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142463837047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_49 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (20597728273643 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284931645549 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨49, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (20597728273643 / 25000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284931645549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_50 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (5147315079683 / 6250000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284935668881 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨50, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (5147315079683 / 6250000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284935668881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_51 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82323192914777 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571234920763 / 25000000000000 : ℝ))
      (E := (cell12440 ⟨51, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82323192914777 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (571234920763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_52 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (16457873597111 / 20000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284943685719 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨52, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (16457873597111 / 20000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284943685719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_53 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82255566458841 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (285618459291 / 12500000000000 : ℝ))
      (E := (cell12440 ⟨53, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82255566458841 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (285618459291 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_54 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41110894153177 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142475852583 / 50000000000000 : ℝ))
      (E := (cell12440 ⟨54, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41110894153177 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (1142475852583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_55 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82188033499959 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284955657177 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨55, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82188033499959 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284955657177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_56 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41077151005829 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (5712399261 / 250000000000 : ℝ))
      (E := (cell12440 ⟨56, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41077151005829 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (5712399261 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_57 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (41060296906797 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284963666219 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨57, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (41060296906797 / 50000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284963666219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_58 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82086908878051 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (71405239289 / 3125000000000 : ℝ))
      (E := (cell12440 ⟨58, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82086908878051 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (71405239289 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12440_59 : CellCertificate 12440 (894099881774877 / 10000000000000000 : ℝ) (1688470501812879 / 1000000000000000000 : ℝ) (170618591862529 / 5000000000000000 : ℝ)
    (cell12440 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · norm_num [cell12440]
  · have h := gap_lower (n := 12440) (a := (82053247177449 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284971673749 / 100000000000000 : ℝ))
      (E := (cell12440 ⟨59, by decide⟩).energy) (xi := (170618591862529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12440 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12440]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12440])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12440) (a := (82053247177449 / 100000000000000 : ℝ)) (b := (41405496147 / 25000000000000 : ℝ)) (q := (2284971673749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12440])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12440]

theorem cert12441_40 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (1033710212849 / 1250000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284761658679 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨40, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (1033710212849 / 1250000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284761658679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_41 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82662733075821 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571191403917 / 25000000000000 : ℝ))
      (E := (cell12441 ⟨41, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82662733075821 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571191403917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_42 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (20657168211613 / 25000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284769634327 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨42, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (20657168211613 / 25000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284769634327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_43 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (516216476937 / 625000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142386827769 / 50000000000000 : ℝ))
      (E := (cell12441 ⟨43, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (516216476937 / 625000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142386827769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_44 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41280311718243 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142388809933 / 50000000000000 : ℝ))
      (E := (cell12441 ⟨44, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41280311718243 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142388809933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_45 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82526634196559 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571195411021 / 25000000000000 : ℝ))
      (E := (cell12441 ⟨45, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82526634196559 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571195411021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_46 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41246334280349 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284785609483 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨46, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41246334280349 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284785609483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_47 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82458726499611 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142394816247 / 50000000000000 : ℝ))
      (E := (cell12441 ⟨47, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82458726499611 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (1142394816247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_48 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82424807984151 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284793652793 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨48, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82424807984151 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284793652793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_49 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (2059772824633 / 2500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (142799850609 / 6250000000000 : ℝ))
      (E := (cell12441 ⟨49, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (2059772824633 / 2500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (142799850609 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_50 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (16471408294853 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (91392064771 / 4000000000000 : ℝ))
      (E := (cell12441 ⟨50, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (16471408294853 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (91392064771 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_51 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82323193422279 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285600702543 / 12500000000000 : ℝ))
      (E := (cell12441 ⟨51, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82323193422279 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285600702543 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_52 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82289368800797 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284809610611 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨52, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82289368800797 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284809610611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_53 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41127783790699 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571203411637 / 25000000000000 : ℝ))
      (E := (cell12441 ⟨53, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41127783790699 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (571203411637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_54 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (16444357947161 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285602208301 / 12500000000000 : ℝ))
      (E := (cell12441 ⟨54, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (16444357947161 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285602208301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_55 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (2054700880897 / 2500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (142801354201 / 6250000000000 : ℝ))
      (E := (cell12441 ⟨55, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (2054700880897 / 2500000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (142801354201 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_56 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (20538576013407 / 25000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285603205723 / 12500000000000 : ℝ))
      (E := (cell12441 ⟨56, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (20538576013407 / 25000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (285603205723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_57 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (82120596161193 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284829657841 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨57, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (82120596161193 / 100000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284829657841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_58 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (41043455765429 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284833640707 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨58, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (41043455765429 / 50000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284833640707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12441_59 : CellCertificate 12441 (894070814075441 / 10000000000000000 : ℝ) (337666947606201 / 200000000000000000 : ℝ) (341209051644083 / 10000000000000000 : ℝ)
    (cell12441 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · norm_num [cell12441]
  · have h := gap_lower (n := 12441) (a := (16410650027009 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284837649741 / 100000000000000 : ℝ))
      (E := (cell12441 ⟨59, by decide⟩).energy) (xi := (341209051644083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12441 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12441]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12441])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12441) (a := (16410650027009 / 20000000000000 : ℝ)) (b := (82804250617 / 50000000000000 : ℝ)) (q := (2284837649741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12441])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12441]

theorem cert12442_40 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (10337101765381 / 12500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284627657907 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨40, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (10337101765381 / 12500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284627657907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_41 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (516642065521 / 625000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284631653487 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨41, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (516642065521 / 625000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284631653487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_42 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (8262867056597 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284635652723 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨42, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (8262867056597 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284635652723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_43 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82594634340987 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284639655217 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨43, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82594634340987 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284639655217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_44 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82560621778671 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284643660351 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨44, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82560621778671 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284643660351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_45 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (10315829106179 / 12500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285580958411 / 12500000000000 : ℝ))
      (E := (cell12442 ⟨45, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (10315829106179 / 12500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (285580958411 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_46 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82492667523831 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142325837487 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨46, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82492667523831 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142325837487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_47 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (41229362886287 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571163905813 / 25000000000000 : ℝ))
      (E := (cell12442 ⟨47, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (41229362886287 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571163905813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_48 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (41212403783259 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284659628383 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨48, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (41212403783259 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284659628383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_49 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (10298864109583 / 12500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142331814901 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨49, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (10298864109583 / 12500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142331814901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_50 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82357041674161 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284667625593 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨50, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82357041674161 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284667625593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_51 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82323193930301 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571167918151 / 25000000000000 : ℝ))
      (E := (cell12442 ⟨51, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82323193930301 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (571167918151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_52 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (2057234240413 / 2500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142337825279 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨52, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (2057234240413 / 2500000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142337825279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_53 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (205638921761 / 250000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (446226499 / 19531250000 : ℝ))
      (E := (cell12442 ⟨53, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (205638921761 / 250000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (446226499 / 19531250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_54 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (41110895582831 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142341812387 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨54, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (41110895582831 / 50000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142341812387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_55 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (8218803697217 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284687674417 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨55, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (8218803697217 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284687674417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_56 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (8215430609593 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284691643467 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨56, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (8215430609593 / 10000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284691643467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_57 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (16424119701817 / 20000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284695646703 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨57, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (16424119701817 / 20000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284695646703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_58 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (82086914183921 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284699680589 / 100000000000000 : ℝ))
      (E := (cell12442 ⟨58, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (82086914183921 / 100000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (2284699680589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12442_59 : CellCertificate 12442 (447020875435783 / 5000000000000000 : ℝ) (21102487450999 / 12500000000000000 : ℝ) (341180924293929 / 10000000000000000 : ℝ)
    (cell12442 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · norm_num [cell12442]
  · have h := gap_lower (n := 12442) (a := (4102662654643 / 5000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142351841109 / 50000000000000 : ℝ))
      (E := (cell12442 ⟨59, by decide⟩).energy) (xi := (341180924293929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12442 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12442]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12442])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12442) (a := (4102662654643 / 5000000000000 : ℝ)) (b := (82797510049 / 50000000000000 : ℝ)) (q := (1142351841109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12442])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12442]

theorem cert12443_40 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41348405609559 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284493712433 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨40, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41348405609559 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284493712433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_41 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (20665681972951 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456899549333 / 20000000000000 : ℝ))
      (E := (cell12443 ⟨41, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (20665681972951 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456899549333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_42 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (16525733657271 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (114225086327 / 5000000000000 : ℝ))
      (E := (cell12443 ⟨42, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (16525733657271 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (114225086327 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_43 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (82594632372881 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142252855191 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨43, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (82594632372881 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142252855191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_44 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (16512124024329 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (71390928049 / 3125000000000 : ℝ))
      (E := (cell12443 ⟨44, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (16512124024329 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (71390928049 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_45 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (5157914468941 / 6250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285564218263 / 12500000000000 : ℝ))
      (E := (cell12443 ⟨45, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (5157914468941 / 6250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285564218263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_46 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (3299706659507 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142258868639 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨46, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (3299706659507 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142258868639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_47 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (82458725046211 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284521728633 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨47, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (82458725046211 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284521728633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_48 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (1030310089369 / 1250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284525718683 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨48, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (1030310089369 / 1250000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284525718683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_49 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41195456384303 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142264852861 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨49, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41195456384303 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142264852861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_50 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (16471408374923 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142266873397 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨50, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (16471408374923 / 20000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142266873397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_51 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (82323194438843 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284537721873 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨51, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (82323194438843 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284537721873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_52 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41144685216363 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456908349311 / 20000000000000 : ℝ))
      (E := (cell12443 ⟨52, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41144685216363 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (456908349311 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_53 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41127784913923 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142272850149 / 50000000000000 : ℝ))
      (E := (cell12443 ⟨53, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41127784913923 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (1142272850149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_54 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (3288871703837 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (35696089037 / 1562500000000 : ℝ))
      (E := (cell12443 ⟨54, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (3288871703837 / 4000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (35696089037 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_55 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (82188038708829 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (17848076077 / 781250000000 : ℝ))
      (E := (cell12443 ⟨55, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (82188038708829 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (17848076077 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_56 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (41077154069281 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284557756549 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨56, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (41077154069281 / 50000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284557756549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_57 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (82120600857271 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285570218881 / 12500000000000 : ℝ))
      (E := (cell12443 ⟨57, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (82120600857271 / 100000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (285570218881 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_58 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (2052172920931 / 2500000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284565717751 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨58, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (2052172920931 / 2500000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284565717751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12443_59 : CellCertificate 12443 (11175158652027 / 125000000000000 : ℝ) (1688063275954357 / 1000000000000000000 : ℝ) (341152801673269 / 10000000000000000 : ℝ)
    (cell12443 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · norm_num [cell12443]
  · have h := gap_lower (n := 12443) (a := (20513314012723 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284569712013 / 100000000000000 : ℝ))
      (E := (cell12443 ⟨59, by decide⟩).energy) (xi := (341152801673269 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12443 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12443]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12443])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12443) (a := (20513314012723 / 25000000000000 : ℝ)) (b := (165581541179 / 100000000000000 : ℝ)) (q := (2284569712013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12443])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12443]

theorem cert12444_40 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82696808316131 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142179911127 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨40, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82696808316131 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142179911127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_41 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82662725301151 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142181918229 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨41, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82662725301151 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142181918229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_42 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (20657166501901 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142183927891 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨42, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (20657166501901 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142183927891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_43 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41297315202801 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285546477629 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨43, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41297315202801 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285546477629 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_44 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41280309232703 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (35693372643 / 1562500000000 : ℝ))
      (E := (cell12444 ⟨44, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41280309232703 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (35693372643 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_45 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82526630157429 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571094955423 / 25000000000000 : ℝ))
      (E := (cell12444 ⟨45, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82526630157429 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571094955423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_46 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (8249266545223 / 10000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285547981907 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨46, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (8249266545223 / 10000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285547981907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_47 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82458724320521 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (456877566173 / 20000000000000 : ℝ))
      (E := (cell12444 ⟨47, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82458724320521 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (456877566173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_48 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41212403366579 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142195932391 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨48, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41212403366579 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142195932391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_49 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (10298864082643 / 12500000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142197918753 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨49, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (10298864082643 / 12500000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142197918753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_50 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (20589260518907 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284399864963 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨50, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (20589260518907 / 25000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284399864963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_51 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41161597473953 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284403827129 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨51, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41161597473953 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284403827129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_52 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (16457874249883 / 20000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142203919799 / 50000000000000 : ℝ))
      (E := (cell12444 ⟨52, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (16457874249883 / 20000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (1142203919799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_53 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82255570951737 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285551480107 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨53, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82255570951737 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285551480107 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_54 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (16444358805319 / 20000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285551978517 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨54, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (16444358805319 / 20000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285551978517 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_55 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (2568376263933 / 3125000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284419857533 / 100000000000000 : ℝ))
      (E := (cell12444 ⟨55, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (2568376263933 / 3125000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (2284419857533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_56 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (3286172407261 / 4000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (142776491677 / 6250000000000 : ℝ))
      (E := (cell12444 ⟨56, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (3286172407261 / 4000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (142776491677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_57 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82120603205749 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571106963159 / 25000000000000 : ℝ))
      (E := (cell12444 ⟨57, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82120603205749 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571106963159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_58 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (82086919490813 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571107967621 / 25000000000000 : ℝ))
      (E := (cell12444 ⟨58, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (82086919490813 / 100000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (571107967621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12444_59 : CellCertificate 12444 (89398363794613 / 1000000000000000 : ℝ) (1687927577649053 / 1000000000000000000 : ℝ) (341124683780777 / 10000000000000000 : ℝ)
    (cell12444 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · norm_num [cell12444]
  · have h := gap_lower (n := 12444) (a := (41026629504571 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285554482183 / 12500000000000 : ℝ))
      (E := (cell12444 ⟨59, by decide⟩).energy) (xi := (341124683780777 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12444 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12444]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12444])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12444) (a := (41026629504571 / 50000000000000 : ℝ)) (b := (82784032239 / 50000000000000 : ℝ)) (q := (285554482183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12444])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12444]

theorem cert12445_40 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41348402707043 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284226046097 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨40, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41348402707043 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284226046097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_41 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82662722711401 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (57105751009 / 2500000000000 : ℝ))
      (E := (cell12445 ⟨41, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82662722711401 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (57105751009 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_42 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82628663729719 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (17845578441 / 781250000000 : ℝ))
      (E := (cell12445 ⟨42, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82628663729719 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (17845578441 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_43 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82594628439149 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456847609193 / 20000000000000 : ℝ))
      (E := (cell12445 ⟨43, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82594628439149 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (456847609193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_44 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (20640154202489 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142121028143 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨44, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (20640154202489 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142121028143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_45 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82526628812551 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (285530751467 / 12500000000000 : ℝ))
      (E := (cell12445 ⟨45, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82526628812551 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (285530751467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_46 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82492664417497 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (142765626807 / 6250000000000 : ℝ))
      (E := (cell12445 ⟨46, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82492664417497 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (142765626807 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_47 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (5153670224719 / 6250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (91370161909 / 4000000000000 : ℝ))
      (E := (cell12445 ⟨47, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (5153670224719 / 6250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (91370161909 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_48 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (8242480631743 / 10000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (91370320311 / 4000000000000 : ℝ))
      (E := (cell12445 ⟨48, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (8242480631743 / 10000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (91370320311 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_49 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41195456277139 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571065506289 / 25000000000000 : ℝ))
      (E := (cell12445 ⟨49, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41195456277139 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571065506289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_50 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (205892605693 / 250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284266039061 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨50, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (205892605693 / 250000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284266039061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_51 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82323195457489 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142135023679 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨51, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82323195457489 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142135023679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_52 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41144686033293 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (22842740477 / 1000000000000 : ℝ))
      (E := (cell12445 ⟨52, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41144686033293 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (22842740477 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_53 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (10281946509509 / 12500000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571069509383 / 25000000000000 : ℝ))
      (E := (cell12445 ⟨53, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (10281946509509 / 12500000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (571069509383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_54 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (10277724432209 / 12500000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284282014083 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨54, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (10277724432209 / 12500000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284282014083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_55 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (20547010545813 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284286033451 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨55, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (20547010545813 / 25000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284286033451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_56 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82154312224819 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284290033419 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨56, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82154312224819 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284290033419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_57 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82120605554521 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284294010587 / 100000000000000 : ℝ))
      (E := (cell12445 ⟨57, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82120605554521 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (2284294010587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_58 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (41043461072321 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142149010249 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨58, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (41043461072321 / 50000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142149010249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12445_59 : CellCertificate 12445 (178790917644477 / 2000000000000000 : ℝ) (1687791901158747 / 1000000000000000000 : ℝ) (2728772564921 / 80000000000000 : ℝ)
    (cell12445 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · norm_num [cell12445]
  · have h := gap_lower (n := 12445) (a := (82053261967609 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142151029703 / 50000000000000 : ℝ))
      (E := (cell12445 ⟨59, by decide⟩).energy) (xi := (2728772564921 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12445 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12445]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12445])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12445) (a := (82053261967609 / 100000000000000 : ℝ)) (b := (20694323749 / 12500000000000 : ℝ)) (q := (1142151029703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12445])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12445]

theorem cert12446_40 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82696802512983 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142046133259 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨40, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82696802512983 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142046133259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_41 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (16532544024511 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142048120439 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨41, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (16532544024511 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142048120439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_42 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41314330726349 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284100280541 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨42, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41314330726349 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284100280541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_43 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41297313236761 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142052133797 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨43, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41297313236761 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142052133797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_44 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82560615155293 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284108260157 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨44, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82560615155293 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284108260157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_45 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82526627468423 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284112257393 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨45, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82526627468423 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284112257393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_46 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41246331691737 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142058129123 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨46, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41246331691737 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142058129123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_47 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82458722871159 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284120261439 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨47, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82458722871159 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284120261439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_48 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (40246487257 / 48828125000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142062132741 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨48, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (40246487257 / 48828125000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142062132741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_49 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82390912448009 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284128268671 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨49, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82390912448009 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284128268671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_50 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82357042479329 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284132269087 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨50, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82357042479329 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284132269087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_51 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (10290399495949 / 12500000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (571034066149 / 25000000000000 : ℝ))
      (E := (cell12446 ⟨51, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (10290399495949 / 12500000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (571034066149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_52 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41144686442119 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (571035063213 / 25000000000000 : ℝ))
      (E := (cell12446 ⟨52, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41144686442119 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (571035063213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_53 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82255573200851 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284144290323 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨53, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82255573200851 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284144290323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_54 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41110898444577 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (228414825621 / 10000000000000 : ℝ))
      (E := (cell12446 ⟨54, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41110898444577 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (228414825621 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_55 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (10273505490127 / 12500000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284152265611 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨55, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (10273505490127 / 12500000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284152265611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_56 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (82154314268443 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284156256309 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨56, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (82154314268443 / 100000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284156256309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_57 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (16424121580717 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284160284027 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨57, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (16424121580717 / 20000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284160284027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_58 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41043462399363 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142082143043 / 50000000000000 : ℝ))
      (E := (cell12446 ⟨58, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41043462399363 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (1142082143043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12446_59 : CellCertificate 12446 (446962771494917 / 5000000000000000 : ℝ) (1687656246478179 / 1000000000000000000 : ℝ) (341068462174989 / 10000000000000000 : ℝ)
    (cell12446 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · norm_num [cell12446]
  · have h := gap_lower (n := 12446) (a := (41026632463147 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284168258667 / 100000000000000 : ℝ))
      (E := (cell12446 ⟨59, by decide⟩).energy) (xi := (341068462174989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12446 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12446]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12446])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12446) (a := (41026632463147 / 50000000000000 : ℝ)) (b := (82770558861 / 50000000000000 : ℝ)) (q := (2284168258667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12446])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12446]

theorem cert12447_40 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82696799612821 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283958542241 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨40, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82696799612821 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283958542241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_41 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (20665679383653 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283962555507 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨41, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (20665679383653 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283962555507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_42 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82628659176541 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283966576063 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨42, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82628659176541 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283966576063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_43 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82594624508721 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141985272357 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨43, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82594624508721 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141985272357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_44 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82560613501417 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283974578399 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨44, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82560613501417 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283974578399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_45 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82526626125043 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283978558669 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨45, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82526626125043 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283978558669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_46 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82492662350163 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283982543259 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨46, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82492662350163 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2283982543259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_47 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82458722147487 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141993265447 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨47, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82458722147487 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141993265447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_48 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (20606201371969 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141995289497 / 50000000000000 : ℝ))
      (E := (cell12447 ⟨48, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (20606201371969 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (1141995289497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_49 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16478182468467 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (285499321007 / 12500000000000 : ℝ))
      (E := (cell12447 ⟨49, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16478182468467 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (285499321007 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_50 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (2573657583813 / 3125000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (456799711009 / 20000000000000 : ℝ))
      (E := (cell12447 ⟨50, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (2573657583813 / 3125000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (456799711009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_51 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16464639295643 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (571000634457 / 25000000000000 : ℝ))
      (E := (cell12447 ⟨51, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16464639295643 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (571000634457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_52 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82289373702373 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284006573063 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨52, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82289373702373 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284006573063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_53 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82255574326073 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (456802108041 / 20000000000000 : ℝ))
      (E := (cell12447 ⟨53, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82255574326073 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (456802108041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_54 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (41110899160521 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284014554517 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨54, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (41110899160521 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284014554517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_55 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (20547011414787 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284018554013 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨55, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (20547011414787 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284018554013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_56 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (41077158156199 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (142751408469 / 6250000000000 : ℝ))
      (E := (cell12447 ⟨56, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (41077158156199 / 50000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (142751408469 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_57 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (82120610252941 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284026554713 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨57, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (82120610252941 / 100000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284026554713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_58 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (16417385490613 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284030548957 / 100000000000000 : ℝ))
      (E := (cell12447 ⟨58, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (16417385490613 / 20000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (2284030548957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12447_59 : CellCertificate 12447 (178779300449477 / 2000000000000000 : ℝ) (1687520613602089 / 1000000000000000000 : ℝ) (341040358459043 / 10000000000000000 : ℝ)
    (cell12447 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · norm_num [cell12447]
  · have h := gap_lower (n := 12447) (a := (20513316971299 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (228403457359 / 10000000000000 : ℝ))
      (E := (cell12447 ⟨59, by decide⟩).energy) (xi := (341040358459043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12447 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12447]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12447])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12447) (a := (20513316971299 / 25000000000000 : ℝ)) (b := (82763823833 / 50000000000000 : ℝ)) (q := (228403457359 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12447])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12447]

theorem cert12448_40 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82696796713601 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283824931987 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨40, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82696796713601 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283824931987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_41 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82662714947571 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283828925501 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨41, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82662714947571 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283828925501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_42 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (645536382041 / 781250000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570958231753 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨42, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (645536382041 / 781250000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570958231753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_43 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41297311272373 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570959219331 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨43, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41297311272373 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570959219331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_44 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82560611848329 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283840893377 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨44, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82560611848329 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283840893377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_45 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82526624782413 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (57096122889 / 2500000000000 : ℝ))
      (E := (cell12448 ⟨45, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82526624782413 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (57096122889 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_46 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82492661317561 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (142740555247 / 6250000000000 : ℝ))
      (E := (cell12448 ⟨46, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82492661317561 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (142740555247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_47 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82458721424487 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283852914979 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨47, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82458721424487 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283852914979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_48 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (1648496101481 / 2000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (11419284447 / 500000000000 : ℝ))
      (E := (cell12448 ⟨48, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (1648496101481 / 2000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (11419284447 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_49 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82390912237257 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283860923307 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨49, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82390912237257 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283860923307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_50 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (4117852144263 / 5000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570966224233 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨50, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (4117852144263 / 5000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570966224233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_51 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82323196989357 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141934463017 / 50000000000000 : ℝ))
      (E := (cell12448 ⟨51, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82323196989357 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141934463017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_52 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82289374520989 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570968222581 / 25000000000000 : ℝ))
      (E := (cell12448 ⟨52, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82289374520989 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (570968222581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_53 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (4112778772587 / 5000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283876905231 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨53, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (4112778772587 / 5000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283876905231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_54 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (10277724969167 / 12500000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283880909003 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨54, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (10277724969167 / 12500000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283880909003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_55 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (5136752962353 / 6250000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283884898657 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨55, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (5136752962353 / 6250000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283884898657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_56 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (41077159178341 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283888930103 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨56, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (41077159178341 / 50000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283888930103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_57 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (8212061260259 / 10000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (456778576353 / 20000000000000 : ℝ))
      (E := (cell12448 ⟨57, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (8212061260259 / 10000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (456778576353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_58 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (82086930107659 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283896927403 / 100000000000000 : ℝ))
      (E := (cell12448 ⟨58, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (82086930107659 / 100000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (2283896927403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12448_59 : CellCertificate 12448 (893867465993947 / 10000000000000000 : ℝ) (843692501262611 / 500000000000000000 : ℝ) (85253064866491 / 2500000000000000 : ℝ)
    (cell12448 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · norm_num [cell12448]
  · have h := gap_lower (n := 12448) (a := (16410654168863 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141950442917 / 50000000000000 : ℝ))
      (E := (cell12448 ⟨59, by decide⟩).energy) (xi := (85253064866491 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12448 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12448]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12448])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12448) (a := (16410654168863 / 20000000000000 : ℝ)) (b := (82757089913 / 50000000000000 : ℝ)) (q := (1141950442917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12448])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12448]

theorem cert12449_40 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82696793815321 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570922829579 / 25000000000000 : ℝ))
      (E := (cell12449 ⟨40, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82696793815321 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570922829579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_41 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82662712361433 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570923823029 / 25000000000000 : ℝ))
      (E := (cell12449 ⟨41, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82662712361433 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (570923823029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_42 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82628654626819 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141849637311 / 50000000000000 : ℝ))
      (E := (cell12449 ⟨42, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82628654626819 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141849637311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_43 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (20648655145399 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (114185166211 / 5000000000000 : ℝ))
      (E := (cell12449 ⟨43, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (20648655145399 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (114185166211 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_44 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82560610196027 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (285463415341 / 12500000000000 : ℝ))
      (E := (cell12449 ⟨44, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82560610196027 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (285463415341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_45 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (8252662344053 / 10000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283711328071 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨45, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (8252662344053 / 10000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283711328071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_46 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (8249266028567 / 10000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141857640163 / 50000000000000 : ℝ))
      (E := (cell12449 ⟨46, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (8249266028567 / 10000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141857640163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_47 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82458720702159 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283719295921 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨47, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82458720702159 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283719295921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_48 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41212402330429 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (91348932581 / 4000000000000 : ℝ))
      (E := (cell12449 ⟨48, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41212402330429 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (91348932581 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_49 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (3295636485311 / 4000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283727275493 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨49, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (3295636485311 / 4000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283727275493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_50 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41178521544531 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (71366602961 / 3125000000000 : ℝ))
      (E := (cell12449 ⟨50, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41178521544531 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (71366602961 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_51 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82323197501019 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283735311253 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨51, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82323197501019 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283735311253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_52 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (41144687670043 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283739322649 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨52, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (41144687670043 / 50000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283739322649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_53 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82255576577849 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283743326379 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨53, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82255576577849 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283743326379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_54 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (20555450296509 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (285468414959 / 12500000000000 : ℝ))
      (E := (cell12449 ⟨54, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (20555450296509 / 25000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (285468414959 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_55 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (16437609827303 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283751299547 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨55, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (16437609827303 / 20000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283751299547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_56 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82154320401297 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (228375532191 / 10000000000000 : ℝ))
      (E := (cell12449 ⟨56, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82154320401297 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (228375532191 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_57 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82120614952531 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283759324309 / 100000000000000 : ℝ))
      (E := (cell12449 ⟨57, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82120614952531 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (2283759324309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_58 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82086932762507 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456752660627 / 20000000000000 : ℝ))
      (E := (cell12449 ⟨58, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82086932762507 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (456752660627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

theorem cert12449_59 : CellCertificate 12449 (89383843422843 / 1000000000000000 : ℝ) (1687249413242323 / 1000000000000000000 : ℝ) (340984165194427 / 10000000000000000 : ℝ)
    (cell12449 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · norm_num [cell12449]
  · have h := gap_lower (n := 12449) (a := (82053273803651 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141883656871 / 50000000000000 : ℝ))
      (E := (cell12449 ⟨59, by decide⟩).energy) (xi := (340984165194427 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12449 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12449]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12449])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12449) (a := (82053273803651 / 100000000000000 : ℝ)) (b := (165500714199 / 100000000000000 : ℝ)) (q := (1141883656871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12449])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12449]

end BstLean.Part268
