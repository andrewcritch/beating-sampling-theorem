import BstLean.Part268CellShard4Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12450_40 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82696790917983 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283557759949 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨40, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82696790917983 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283557759949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_41 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82662709776197 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (456712354569 / 20000000000000 : ℝ))
      (E := (cell12450 ⟨41, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82662709776197 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (456712354569 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_42 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41314326176627 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283565736431 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨42, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41314326176627 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283565736431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_43 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82594618619271 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141784883909 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨43, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82594618619271 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141784883909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_44 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (322502377127 / 390625000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (114178687441 / 5000000000000 : ℝ))
      (E := (cell12450 ⟨44, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (322502377127 / 390625000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (114178687441 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_45 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (20631655524849 / 25000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283577737361 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨45, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (20631655524849 / 25000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283577737361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_46 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (10311582406811 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (71361929137 / 3125000000000 : ℝ))
      (E := (cell12450 ⟨46, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (10311582406811 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (71361929137 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_47 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41229359990251 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (228358573261 / 10000000000000 : ℝ))
      (E := (cell12450 ⟨47, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41229359990251 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (228358573261 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_48 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82424804248299 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283589736547 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨48, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82424804248299 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283589736547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_49 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (10298864003611 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141796871243 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨49, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (10298864003611 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141796871243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_50 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41178521646711 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (456719549701 / 20000000000000 : ℝ))
      (E := (cell12450 ⟨50, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41178521646711 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (456719549701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_51 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (205807995033 / 250000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570900438117 / 25000000000000 : ℝ))
      (E := (cell12450 ⟨51, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (205807995033 / 250000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570900438117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_52 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (16457875231933 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141802876013 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨52, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (16457875231933 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141802876013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_53 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41127788852201 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283609744619 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨53, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41127788852201 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283609744619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_54 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82221802619141 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570903446631 / 25000000000000 : ℝ))
      (E := (cell12450 ⟨54, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82221802619141 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570903446631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_55 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (328752203503 / 400000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141808878341 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨55, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (328752203503 / 400000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141808878341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_56 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41077161223121 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285452721253 / 12500000000000 : ℝ))
      (E := (cell12450 ⟨56, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41077161223121 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285452721253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_57 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (16424123460553 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283625764099 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨57, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (16424123460553 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283625764099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_58 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (8208693541761 / 10000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570907448611 / 25000000000000 : ℝ))
      (E := (cell12450 ⟨58, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (8208693541761 / 10000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570907448611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_59 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (20513319190801 / 25000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2230111131 / 97656250000 : ℝ))
      (E := (cell12450 ⟨59, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (20513319190801 / 25000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2230111131 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12451_40 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (5168549251349 / 6250000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285428032111 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨40, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (5168549251349 / 6250000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285428032111 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_41 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41331353595931 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283428250197 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨41, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41331353595931 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283428250197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_42 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (10328581260069 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283432253673 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨42, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (10328581260069 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283432253673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_43 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (8259461665777 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283436266911 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨43, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (8259461665777 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283436266911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_44 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (10320075861723 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456688057857 / 20000000000000 : ℝ))
      (E := (cell12451 ⟨44, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (10320075861723 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456688057857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_45 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (8252662075901 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285430532639 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨45, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (8252662075901 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285430532639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_46 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (5155791139001 / 6250000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570862060031 / 25000000000000 : ℝ))
      (E := (cell12451 ⟨46, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (5155791139001 / 6250000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570862060031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_47 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (82458719259517 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283452283931 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨47, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (82458719259517 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283452283931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_48 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41212401918187 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283456273287 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨48, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41212401918187 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283456273287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_49 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (20597727981399 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283460265349 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨49, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (20597727981399 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283460265349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_50 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41178521749169 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283464258193 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨50, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41178521749169 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283464258193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_51 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (823231985259 / 1000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (28543353121 / 1250000000000 : ℝ))
      (E := (cell12451 ⟨51, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (823231985259 / 1000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (28543353121 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_52 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (20572344244931 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283472296469 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨52, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (20572344244931 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283472296469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_53 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41127789415699 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285434534751 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨53, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41127789415699 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285434534751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_54 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (82221804052651 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283480250509 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨54, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (82221804052651 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283480250509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_55 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (82188052615353 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141742135031 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨55, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (82188052615353 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141742135031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_56 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (20538581122879 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283488274447 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨56, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (20538581122879 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283488274447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_57 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (8212061965329 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283492260261 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨57, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (8212061965329 / 10000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283492260261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_58 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41043469036483 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141748141521 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨58, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41043469036483 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141748141521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_59 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41026639861487 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (228350027987 / 10000000000000 : ℝ))
      (E := (cell12451 ⟨59, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41026639861487 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (228350027987 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12452_40 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41348392563063 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283290809133 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨40, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41348392563063 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283290809133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_41 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82662704608429 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456658968333 / 20000000000000 : ℝ))
      (E := (cell12452 ⟨41, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82662704608429 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456658968333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_42 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82628647808713 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570824706587 / 25000000000000 : ℝ))
      (E := (cell12452 ⟨42, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82628647808713 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570824706587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_43 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (16518922939419 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283302821499 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨43, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (16518922939419 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283302821499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_44 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41280302621921 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283306826493 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨44, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41280302621921 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283306826493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_45 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (20631654854843 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456662168097 / 20000000000000 : ℝ))
      (E := (cell12452 ⟨45, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (20631654854843 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456662168097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_46 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41246328597127 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (45666296071 / 2000000000000 : ℝ))
      (E := (cell12452 ⟨46, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41246328597127 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (45666296071 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_47 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82458718539203 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (142707427007 / 6250000000000 : ℝ))
      (E := (cell12452 ⟨47, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82458718539203 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (142707427007 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_48 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82424803425081 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (142707675433 / 6250000000000 : ℝ))
      (E := (cell12452 ⟨48, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82424803425081 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (142707675433 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_49 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82390911822899 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141663422043 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨49, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82390911822899 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141663422043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_50 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82357043703811 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456666164763 / 20000000000000 : ℝ))
      (E := (cell12452 ⟨50, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82357043703811 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456666164763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_51 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41161599519559 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (142708428867 / 6250000000000 : ℝ))
      (E := (cell12452 ⟨51, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41161599519559 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (142708428867 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_52 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (16457875560053 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456667767593 / 20000000000000 : ℝ))
      (E := (cell12452 ⟨52, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (16457875560053 / 20000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456667767593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_53 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82255579958837 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570835702123 / 25000000000000 : ℝ))
      (E := (cell12452 ⟨53, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82255579958837 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570835702123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_54 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41110902743283 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (228334682973 / 10000000000000 : ℝ))
      (E := (cell12452 ⟨54, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41110902743283 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (228334682973 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_55 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82188054355323 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (228335083969 / 10000000000000 : ℝ))
      (E := (cell12452 ⟨55, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82188054355323 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (228335083969 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_56 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82154326537119 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (114167741759 / 5000000000000 : ℝ))
      (E := (cell12452 ⟨56, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82154326537119 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (114167741759 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_57 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82120622004107 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456671762559 / 20000000000000 : ℝ))
      (E := (cell12452 ⟨57, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82120622004107 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (456671762559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_58 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41043470364289 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283362828071 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨58, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41043470364289 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283362828071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_59 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (1025666033537 / 1250000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283366818093 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨59, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (1025666033537 / 1250000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283366818093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12453_40 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (10337097778951 / 12500000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (228315747541 / 10000000000000 : ℝ))
      (E := (cell12453 ⟨40, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (10337097778951 / 12500000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (228315747541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_41 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41331351012949 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141580714879 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨41, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41331351012949 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141580714879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_42 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82628645537737 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141582727229 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨42, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82628645537737 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141582727229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_43 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82594612737243 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141584715793 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨43, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82594612737243 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141584715793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_44 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (16512120718937 / 20000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141586709631 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨44, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (16512120718937 / 20000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141586709631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_45 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41263309040241 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283177475481 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨45, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41263309040241 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283177475481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_46 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82492656165201 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283181422661 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨46, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82492656165201 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283181422661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_47 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (2061467945489 / 2500000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283185436043 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨47, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (2061467945489 / 2500000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283185436043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_48 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82424803014421 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570797363823 / 25000000000000 : ℝ))
      (E := (cell12453 ⟨48, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82424803014421 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570797363823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_49 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (20597727930199 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141596709881 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨49, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (20597727930199 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141596709881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_50 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82357043909841 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (18265579563 / 800000000000 : ℝ))
      (E := (cell12453 ⟨50, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82357043909841 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (18265579563 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_51 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (16464639910571 / 20000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141600735541 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨51, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (16464639910571 / 20000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141600735541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_52 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41144689310643 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570801358881 / 25000000000000 : ℝ))
      (E := (cell12453 ⟨52, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41144689310643 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570801358881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_53 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82255581086719 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283209454129 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨53, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82255581086719 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283209454129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_54 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82221806920887 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141606732569 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨54, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82221806920887 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141606732569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_55 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (4109402804783 / 5000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (71350545799 / 3125000000000 : ℝ))
      (E := (cell12453 ⟨55, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (4109402804783 / 5000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (71350545799 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_56 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (20538582145763 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (35675335191 / 1562500000000 : ℝ))
      (E := (cell12453 ⟨56, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (20538582145763 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (35675335191 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_57 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (5132539022201 / 6250000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (91329019233 / 4000000000000 : ℝ))
      (E := (cell12453 ⟨57, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (5132539022201 / 6250000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (91329019233 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_58 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82086943384443 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570807372171 / 25000000000000 : ℝ))
      (E := (cell12453 ⟨58, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82086943384443 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570807372171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_59 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82053285643163 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283233471983 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨59, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82053285643163 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283233471983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12454_40 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82696779338029 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141512069137 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨40, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82696779338029 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141512069137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_41 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82662699444267 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283028131971 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨41, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82662699444267 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283028131971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_42 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82628643267623 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570758034501 / 25000000000000 : ℝ))
      (E := (cell12454 ⟨42, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82628643267623 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570758034501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_43 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (10324326347277 / 12500000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (228303609717 / 10000000000000 : ℝ))
      (E := (cell12454 ⟨43, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (10324326347277 / 12500000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (228303609717 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_44 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41280300973157 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283040126409 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨44, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41280300973157 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283040126409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_45 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41263308371169 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141522053631 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨45, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41263308371169 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141522053631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_46 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82492655136857 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (114152404873 / 5000000000000 : ℝ))
      (E := (cell12454 ⟨46, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82492655136857 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (114152404873 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_47 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82458717100587 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570763023931 / 25000000000000 : ℝ))
      (E := (cell12454 ⟨47, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82458717100587 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570763023931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_48 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41212401302197 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283056100557 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨48, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41212401302197 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283056100557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_49 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (10298863952411 / 12500000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (285382513781 / 12500000000000 : ℝ))
      (E := (cell12454 ⟨49, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (10298863952411 / 12500000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (285382513781 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_50 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82357044116427 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (285383015359 / 12500000000000 : ℝ))
      (E := (cell12454 ⟨50, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82357044116427 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (285383015359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_51 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82323200067111 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283068136291 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨51, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82323200067111 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283068136291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_52 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82289379442787 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283072148151 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨52, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82289379442787 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283072148151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_53 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82255582215043 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141538048431 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨53, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82255582215043 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141538048431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_54 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82221808355611 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283080097681 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨54, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82221808355611 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283080097681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_55 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (20547014459091 / 25000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141542073847 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨55, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (20547014459091 / 25000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141542073847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_56 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41077165314657 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283088125579 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨56, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41077165314657 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283088125579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_57 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (10265078338327 / 12500000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141546073053 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨57, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (10265078338327 / 12500000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141546073053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_58 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41043473020281 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141548073293 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨58, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41043473020281 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141548073293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_59 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41026644301791 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141550061601 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨59, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41026644301791 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141550061601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12455_40 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (82696776445389 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282890856449 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨40, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (82696776445389 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282890856449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_41 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (82662696863537 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (228289483081 / 10000000000000 : ℝ))
      (E := (cell12455 ⟨41, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (82662696863537 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (228289483081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_42 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (20657160249593 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141449409107 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨42, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (20657160249593 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141449409107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_43 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (20648652205003 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141451409127 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨43, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (20648652205003 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141451409127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_44 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (10320075037341 / 12500000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282906830301 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨44, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (10320075037341 / 12500000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282906830301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_45 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41263307702471 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282910853507 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨45, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41263307702471 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282910853507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_46 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41246327054611 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141457413973 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨46, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41246327054611 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141457413973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_47 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41229358191143 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282918870041 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨47, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41229358191143 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282918870041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_48 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (82424802194999 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141461430273 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨48, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (82424802194999 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141461430273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_49 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (659127292147 / 800000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282926856609 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨49, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (659127292147 / 800000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282926856609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_50 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (82357044323569 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570732714077 / 25000000000000 : ℝ))
      (E := (cell12455 ⟨50, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (82357044323569 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570732714077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_51 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16464640116377 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282934857501 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨51, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16464640116377 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282934857501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_52 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (82289380264769 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456587771567 / 20000000000000 : ℝ))
      (E := (cell12455 ⟨52, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (82289380264769 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456587771567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_53 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (8225558334381 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282942854749 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨53, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (8225558334381 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282942854749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_54 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (82221809790741 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (285368355683 / 12500000000000 : ℝ))
      (E := (cell12455 ⟨54, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (82221809790741 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (285368355683 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_55 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16437611915487 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456590165399 / 20000000000000 : ℝ))
      (E := (cell12455 ⟨55, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16437611915487 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456590165399 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_56 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41077166337953 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141477427623 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨56, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41077166337953 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141477427623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_57 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (20530157264577 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (28536985847 / 1250000000000 : ℝ))
      (E := (cell12455 ⟨57, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (20530157264577 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (28536985847 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_58 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16417389739387 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570740715231 / 25000000000000 : ℝ))
      (E := (cell12455 ⟨58, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16417389739387 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (570740715231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_59 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41026645782109 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141483415459 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨59, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41026645782109 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141483415459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12456_40 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82696773553689 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282757629933 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨40, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82696773553689 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282757629933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_41 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (20665673570927 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (228276164377 / 10000000000000 : ℝ))
      (E := (cell12456 ⟨41, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (20665673570927 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (228276164377 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_42 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41314319364991 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141382806317 / 50000000000000 : ℝ))
      (E := (cell12456 ⟨42, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41314319364991 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141382806317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_43 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (10324325857829 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141384797419 / 50000000000000 : ℝ))
      (E := (cell12456 ⟨43, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (10324325857829 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141384797419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_44 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (10320074831491 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282773648573 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨44, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (10320074831491 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282773648573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_45 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (20631653517073 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141388798269 / 50000000000000 : ℝ))
      (E := (cell12456 ⟨45, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (20631653517073 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141388798269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_46 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (16498530616459 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282781614121 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨46, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (16498530616459 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282781614121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_47 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41229357832327 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (285348205153 / 12500000000000 : ℝ))
      (E := (cell12456 ⟨47, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41229357832327 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (285348205153 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_48 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82424801786237 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282789617437 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨48, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82424801786237 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282789617437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_49 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (16478182283611 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282793599913 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨49, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (16478182283611 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282793599913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_50 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82357044531267 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282797645683 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨50, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82357044531267 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282797645683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_51 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (10290400137147 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282801634713 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨51, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (10290400137147 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282801634713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_52 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (8228938108723 / 10000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456561124717 / 20000000000000 : ℝ))
      (E := (cell12456 ⟨52, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (8228938108723 / 10000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456561124717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_53 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82255584473019 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282809609733 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨53, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82255584473019 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282809609733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_54 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41110905613137 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282813649437 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨54, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41110905613137 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282813649437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_55 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (10273507664859 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282817621623 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨55, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (10273507664859 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282817621623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_56 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41077167361413 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282821641227 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨56, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41077167361413 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282821641227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_57 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82120631410291 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282825645791 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨57, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82120631410291 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282825645791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_58 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82086951353561 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282829631701 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨58, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82086951353561 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282829631701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_59 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82053294525069 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456566730861 / 20000000000000 : ℝ))
      (E := (cell12456 ⟨59, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82053294525069 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456566730861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12457_40 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82696770662927 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282624458733 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨40, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82696770662927 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282624458733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_41 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41331345852389 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282628453361 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨41, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41331345852389 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282628453361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_42 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41314318231227 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282632462493 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨42, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41314318231227 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282632462493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_43 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (3303784196243 / 4000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282636485719 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨43, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (3303784196243 / 4000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282636485719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_44 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (10320074625739 / 12500000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141320231797 / 50000000000000 : ℝ))
      (E := (cell12457 ⟨44, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (10320074625739 / 12500000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141320231797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_45 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82526612732389 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141322227019 / 50000000000000 : ℝ))
      (E := (cell12457 ⟨45, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82526612732389 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141322227019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_46 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (20623163014019 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570662113997 / 25000000000000 : ℝ))
      (E := (cell12457 ⟨46, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (20623163014019 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570662113997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_47 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82458714947693 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (7133288963 / 312500000000 : ℝ))
      (E := (cell12457 ⟨47, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82458714947693 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (7133288963 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_48 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41212400689053 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456531286029 / 20000000000000 : ℝ))
      (E := (cell12457 ⟨48, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41212400689053 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456531286029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_49 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82390911318329 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282660458031 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨49, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82390911318329 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282660458031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_50 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82357044739521 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282664432041 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨50, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82357044739521 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282664432041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_51 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41161600806493 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282668467929 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨51, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41161600806493 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282668467929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_52 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (20572345477543 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (11413362227 / 500000000000 : ℝ))
      (E := (cell12457 ⟨52, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (20572345477543 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (11413362227 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_53 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82255585602669 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282676479877 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨53, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82255585602669 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282676479877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_54 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (20555453165553 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282680450547 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨54, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (20555453165553 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282680450547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_55 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (3287522522427 / 4000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141342236253 / 50000000000000 : ℝ))
      (E := (cell12457 ⟨55, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (3287522522427 / 4000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141342236253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_56 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41077168385037 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (91307539341 / 4000000000000 : ℝ))
      (E := (cell12457 ⟨56, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41077168385037 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (91307539341 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_57 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (16424126752513 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (11413462401 / 500000000000 : ℝ))
      (E := (cell12457 ⟨57, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (16424126752513 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (11413462401 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_58 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82086954010441 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282696458917 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨58, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82086954010441 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282696458917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_59 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82053297486137 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282700475023 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨59, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82053297486137 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282700475023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12458_40 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82696767773103 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456498268569 / 20000000000000 : ℝ))
      (E := (cell12458 ⟨40, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82696767773103 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456498268569 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_41 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82662689126749 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141247659163 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨41, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82662689126749 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141247659163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_42 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82628634195787 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282499367791 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨42, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82628634195787 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282499367791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_43 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (4129730147517 / 5000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456500662903 / 20000000000000 : ℝ))
      (E := (cell12458 ⟨43, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (4129730147517 / 5000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456500662903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_44 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82560595360681 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282507334179 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨44, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82560595360681 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282507334179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_45 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (5157913212327 / 6250000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141255683583 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨45, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (5157913212327 / 6250000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141255683583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_46 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (16498530206113 / 20000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456503070709 / 20000000000000 : ℝ))
      (E := (cell12458 ⟨46, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (16498530206113 / 20000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456503070709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_47 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82458714231401 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282519350849 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨47, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82458714231401 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282519350849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_48 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82424800970607 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282523357581 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨48, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82424800970607 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282523357581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_49 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82390911219197 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141263686013 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨49, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82390911219197 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141263686013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_50 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82357044948331 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141265666649 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨50, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82357044948331 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141265666649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_51 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82323202129313 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570633839287 / 25000000000000 : ℝ))
      (E := (cell12458 ⟨51, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82323202129313 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570633839287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_52 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82289382733593 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282539323281 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨52, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82289382733593 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282539323281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_53 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41127793366381 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282543347119 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨53, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41127793366381 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282543347119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_54 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41110907049277 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282547366901 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨54, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41110907049277 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282547366901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_55 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (16437612960569 / 20000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (57063784491 / 2500000000000 : ℝ))
      (E := (cell12458 ⟨55, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (16437612960569 / 20000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (57063784491 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_56 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (20538584704413 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570638830759 / 25000000000000 : ℝ))
      (E := (cell12458 ⟨56, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (20538584704413 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570638830759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_57 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (8212063611513 / 10000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456511874197 / 20000000000000 : ℝ))
      (E := (cell12458 ⟨57, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (8212063611513 / 10000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456511874197 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_58 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41043478333787 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570640835643 / 25000000000000 : ℝ))
      (E := (cell12458 ⟨58, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41043478333787 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (570640835643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_59 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (4102665022371 / 5000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282567352243 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨59, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (4102665022371 / 5000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282567352243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12459_40 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41348382442109 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282358282273 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨40, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41348382442109 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282358282273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_41 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82662686549619 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282362297419 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨41, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82662686549619 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282362297419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_42 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41314315964991 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (7132394593 / 312500000000 : ℝ))
      (E := (cell12459 ⟨42, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41314315964991 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (7132394593 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_43 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82594600995429 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285296282201 / 12500000000000 : ℝ))
      (E := (cell12459 ⟨43, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82594600995429 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285296282201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_44 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41280296858117 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282374260333 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨44, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41280296858117 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282374260333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_45 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82526610062821 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570594569271 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨45, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82526610062821 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570594569271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_46 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82492650005763 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (456476461359 / 20000000000000 : ℝ))
      (E := (cell12459 ⟨46, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82492650005763 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (456476461359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_47 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82458713515779 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (456477257859 / 20000000000000 : ℝ))
      (E := (cell12459 ⟨47, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82458713515779 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (456477257859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_48 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82424800563739 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570597570481 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨48, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82424800563739 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570597570481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_49 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41195455560329 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285299285371 / 12500000000000 : ℝ))
      (E := (cell12459 ⟨49, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41195455560329 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285299285371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_50 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (16471409031539 / 20000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (4564796581 / 200000000000 : ℝ))
      (E := (cell12459 ⟨50, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (16471409031539 / 20000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (4564796581 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_51 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41161601323079 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141201151187 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨51, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41161601323079 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141201151187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_52 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41144691778747 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282406316237 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨52, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41144691778747 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282406316237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_53 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (321310890091 / 390625000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570602567623 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨53, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (321310890091 / 390625000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570602567623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_54 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (822218155353 / 1000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (456482856079 / 20000000000000 : ℝ))
      (E := (cell12459 ⟨54, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (822218155353 / 1000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (456482856079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_55 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82188066545381 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282418283953 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨55, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82188066545381 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282418283953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_56 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82154340865557 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282422277967 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨56, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82154340865557 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282422277967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_57 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (16424127693597 / 20000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282426318151 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨57, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (16424127693597 / 20000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282426318151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_58 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82086959324961 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570607570667 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨58, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82086959324961 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570607570667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_59 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82053303408919 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141217142983 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨59, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82053303408919 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141217142983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12460_40 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82696761996271 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (285278159627 / 12500000000000 : ℝ))
      (E := (cell12460 ⟨40, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82696761996271 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (285278159627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_41 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (20665670993347 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (285278659143 / 12500000000000 : ℝ))
      (E := (cell12460 ⟨41, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (20665670993347 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (285278659143 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_42 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82628629665037 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141116642971 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨42, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82628629665037 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141116642971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_43 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (4129729952067 / 5000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282237256207 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨43, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (4129729952067 / 5000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282237256207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_44 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (20640148018143 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282241300871 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨44, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (20640148018143 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282241300871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_45 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (20631652182289 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282245301473 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨45, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (20631652182289 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282245301473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_46 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82492648981667 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141124628437 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨46, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82492648981667 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141124628437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_47 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41229356400413 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (285281660437 / 12500000000000 : ℝ))
      (E := (cell12460 ⟨47, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41229356400413 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (285281660437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_48 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82424800157503 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456451452417 / 20000000000000 : ℝ))
      (E := (cell12460 ⟨48, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82424800157503 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456451452417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_49 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (10298863877839 / 12500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (8915083007 / 390625000000 : ℝ))
      (E := (cell12460 ⟨49, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (10298863877839 / 12500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (8915083007 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_50 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (1286828833869 / 1562500000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570566325911 / 25000000000000 : ℝ))
      (E := (cell12460 ⟨50, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (1286828833869 / 1562500000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570566325911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_51 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82323203163519 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141134651803 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨51, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82323203163519 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141134651803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_52 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41144692190937 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456454661251 / 20000000000000 : ℝ))
      (E := (cell12460 ⟨52, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41144692190937 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456454661251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_53 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (2570487156071 / 3125000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (91291092361 / 4000000000000 : ℝ))
      (E := (cell12460 ⟨53, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (2570487156071 / 3125000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (91291092361 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_54 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82221816972449 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (142642581821 / 6250000000000 : ℝ))
      (E := (cell12460 ⟨54, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82221816972449 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (142642581821 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_55 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82188068288283 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141142651799 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨55, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82188068288283 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141142651799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_56 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82154342913791 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141144644607 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨56, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82154342913791 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141144644607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_57 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82120640821131 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282293262573 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨57, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82120640821131 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282293262573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_58 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (410434809913 / 500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282297279207 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨58, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (410434809913 / 500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282297279207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_59 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82053306370633 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282301276193 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨59, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82053306370633 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282301276193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12461_40 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82696759109261 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282092327079 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨40, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82696759109261 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282092327079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_41 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82662681398057 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282096304249 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨41, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82662681398057 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282096304249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_42 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82628627400953 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141050149399 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨42, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82628627400953 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141050149399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_43 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41297298544037 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285263038789 / 12500000000000 : ℝ))
      (E := (cell12461 ⟨43, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41297298544037 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285263038789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_44 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82560590429693 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141054169081 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨44, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82560590429693 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141054169081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_45 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82526607396237 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141056161327 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨45, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82526607396237 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141056161327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_46 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82492647958279 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282116321513 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨46, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82492647958279 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282116321513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_47 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82458712086543 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (456424066691 / 20000000000000 : ℝ))
      (E := (cell12461 ⟨47, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82458712086543 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (456424066691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_48 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82424799751897 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282124298067 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨48, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82424799751897 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282124298067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_49 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82390910925359 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141064165717 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨49, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82390910925359 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141064165717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_50 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82357045578091 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (142633269611 / 6250000000000 : ℝ))
      (E := (cell12461 ⟨50, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82357045578091 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (142633269611 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_51 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41161601840699 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282136301863 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨51, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41161601840699 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282136301863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_52 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82289385206733 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285267544043 / 12500000000000 : ℝ))
      (E := (cell12461 ⟨52, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82289385206733 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285267544043 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_53 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82255590125689 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282144344661 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨53, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82255590125689 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282144344661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_54 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41110909205001 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282148335019 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨54, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41110909205001 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282148335019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_55 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82188070031551 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285269040053 / 12500000000000 : ℝ))
      (E := (cell12461 ⟨55, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82188070031551 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285269040053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_56 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82154344962353 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (114107817839 / 5000000000000 : ℝ))
      (E := (cell12461 ⟨56, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82154344962353 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (114107817839 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_57 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (10265080396821 / 12500000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (912864129 / 40000000000 : ℝ))
      (E := (cell12461 ⟨57, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (10265080396821 / 12500000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (912864129 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_58 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82086964640493 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282164332189 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨58, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82086964640493 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282164332189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_59 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82053309332563 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141084161463 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨59, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82053309332563 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141084161463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12462_40 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (20674189055797 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281959432459 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨40, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (20674189055797 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281959432459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_41 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (10332834852953 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281963449483 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨41, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (10332834852953 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281963449483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_42 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (8262862513773 / 10000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281967425867 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨42, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (8262862513773 / 10000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281967425867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_43 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82594595135629 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140985709963 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨43, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82594595135629 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140985709963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_44 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41280294393799 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281975431023 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨44, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41280294393799 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281975431023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_45 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82526606064063 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281979399467 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨45, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82526606064063 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281979399467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_46 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82492646935599 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281983441847 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨46, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82492646935599 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281983441847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_47 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (644208682601 / 781250000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281987439173 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨47, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (644208682601 / 781250000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281987439173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_48 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82424799346923 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140995724391 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨48, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82424799346923 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140995724391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_49 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82390910828599 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281995410023 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨49, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82390910828599 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281995410023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_50 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (257365768091 / 312500000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281999438813 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨50, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (257365768091 / 312500000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281999438813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_51 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41161602099897 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2282003415111 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨51, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41161602099897 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2282003415111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_52 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82289386032071 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2282007454503 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨52, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82289386032071 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2282007454503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_53 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82255591257547 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2282011436431 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨53, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82255591257547 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2282011436431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_54 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41110909923979 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (285251927137 / 12500000000000 : ℝ))
      (E := (cell12462 ⟨54, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41110909923979 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (285251927137 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_55 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (5136754485949 / 6250000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (456403890517 / 20000000000000 : ℝ))
      (E := (cell12462 ⟨55, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (5136754485949 / 6250000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (456403890517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_56 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82154347011243 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1141011710783 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨56, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82154347011243 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1141011710783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_57 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (16424129105659 / 20000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (285253429851 / 12500000000000 : ℝ))
      (E := (cell12462 ⟨57, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (16424129105659 / 20000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (285253429851 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_58 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (41043483649319 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (142626965101 / 6250000000000 : ℝ))
      (E := (cell12462 ⟨58, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (41043483649319 / 50000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (142626965101 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_59 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (20513328073677 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (456407085233 / 20000000000000 : ℝ))
      (E := (cell12462 ⟨59, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (20513328073677 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (456407085233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12463_40 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82696753338053 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281826593159 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨40, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82696753338053 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281826593159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_41 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (8266267625009 / 10000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285228823919 / 12500000000000 : ℝ))
      (E := (cell12463 ⟨41, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (8266267625009 / 10000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285228823919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_42 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41314311437683 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281834549613 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨42, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41314311437683 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281834549613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_43 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41297296592003 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281838585047 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨43, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41297296592003 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281838585047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_44 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41280293573143 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (456368515891 / 20000000000000 : ℝ))
      (E := (cell12463 ⟨44, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41280293573143 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (456368515891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_45 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41263302366317 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (456369318151 / 20000000000000 : ℝ))
      (E := (cell12463 ⟨45, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41263302366317 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (456369318151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_46 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (659941167309 / 800000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281850559013 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨46, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (659941167309 / 800000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281850559013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_47 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82458710659983 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285231825081 / 12500000000000 : ℝ))
      (E := (cell12463 ⟨47, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82458710659983 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285231825081 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_48 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82424798942579 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140929298203 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨48, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82424798942579 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140929298203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_49 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (5149431920777 / 6250000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285232825429 / 12500000000000 : ℝ))
      (E := (cell12463 ⟨49, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (5149431920777 / 6250000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285232825429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_50 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (16471409200141 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (570466640209 / 25000000000000 : ℝ))
      (E := (cell12463 ⟨50, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (16471409200141 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (570466640209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_51 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41161602359353 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281870584369 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨51, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41161602359353 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281870584369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_52 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82289386857887 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281874553729 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨52, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82289386857887 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281874553729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_53 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (16451118477969 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (456375716867 / 20000000000000 : ℝ))
      (E := (cell12463 ⟨53, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (16451118477969 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (456375716867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_54 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82221821286317 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281882555371 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨54, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82221821286317 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281882555371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_55 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82188073519183 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140943290963 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨55, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82188073519183 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140943290963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_56 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82154349060461 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281890601773 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨56, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82154349060461 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281890601773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_57 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (10265080985289 / 12500000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281894611499 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨57, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (10265080985289 / 12500000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281894611499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_58 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (20521742489259 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140949303743 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨58, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (20521742489259 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140949303743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_59 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (20513328814267 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (228190258591 / 10000000000000 : ℝ))
      (E := (cell12463 ⟨59, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (20513328814267 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (228190258591 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12464_40 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41348375226927 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (285211718807 / 12500000000000 : ℝ))
      (E := (cell12464 ⟨40, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41348375226927 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (285211718807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_41 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41331336838727 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456339557721 / 20000000000000 : ℝ))
      (E := (cell12464 ⟨41, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41331336838727 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456339557721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_42 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41314310306931 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (285212723447 / 12500000000000 : ℝ))
      (E := (cell12464 ⟨42, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41314310306931 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (285212723447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_43 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (20648647808301 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140852902839 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨43, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (20648647808301 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140852902839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_44 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82560585505757 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (114085489173 / 5000000000000 : ℝ))
      (E := (cell12464 ⟨44, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82560585505757 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (114085489173 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_45 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (1650532068039 / 2000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140856889419 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨45, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (1650532068039 / 2000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140856889419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_46 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82492644892357 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281717790743 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨46, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82492644892357 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281717790743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_47 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16491741989541 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140860879499 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨47, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16491741989541 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140860879499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_48 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16484959707773 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140862899927 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨48, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16484959707773 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140862899927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_49 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82390910636857 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (8913007007 / 390625000000 : ℝ))
      (E := (cell12464 ⟨49, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82390910636857 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (8913007007 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_50 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82357046212843 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281733797769 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨50, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82357046212843 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281733797769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_51 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41161602619067 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140868904819 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨51, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41161602619067 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140868904819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_52 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82289387684183 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281741768033 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨52, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82289387684183 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281741768033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_53 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16451118704517 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140872894187 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨53, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16451118704517 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140872894187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_54 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (2055545568127 / 2500000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456349961779 / 20000000000000 : ℝ))
      (E := (cell12464 ⟨54, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (2055545568127 / 2500000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456349961779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_55 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41094037631773 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281753767529 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨55, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41094037631773 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281753767529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_56 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41077175555003 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140878889601 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨56, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41077175555003 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140878889601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_57 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82120650236619 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281761781451 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨57, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82120650236619 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281761781451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_58 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41043486307843 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (71305180333 / 3125000000000 : ℝ))
      (E := (cell12464 ⟨58, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41043486307843 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (71305180333 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_59 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82053318219643 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570442450541 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨59, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82053318219643 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570442450541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12465_40 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82696747570591 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281561021799 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨40, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82696747570591 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281561021799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_41 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20665667776429 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281565041243 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨41, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20665667776429 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281565041243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_42 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (41314309176609 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456313804443 / 20000000000000 : ℝ))
      (E := (cell12465 ⟨42, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (41314309176609 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456313804443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_43 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (10324323660403 / 12500000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (91262920921 / 4000000000000 : ℝ))
      (E := (cell12465 ⟨43, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (10324323660403 / 12500000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (91262920921 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_44 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20640145966503 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281577043037 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨44, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20640145966503 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281577043037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_45 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (8252660207201 / 10000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570395255639 / 25000000000000 : ℝ))
      (E := (cell12465 ⟨45, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (8252660207201 / 10000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570395255639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_46 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20623160967949 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140792509653 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨46, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20623160967949 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140792509653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_47 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (644208665907 / 781250000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570397257999 / 25000000000000 : ℝ))
      (E := (cell12465 ⟨47, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (644208665907 / 781250000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570397257999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_48 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (41212399067891 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140796529563 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨48, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (41212399067891 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140796529563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_49 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (41195455270937 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140798520019 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨49, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (41195455270937 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140798520019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_50 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (1286828850399 / 1562500000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (228160103169 / 10000000000000 : ℝ))
      (E := (cell12465 ⟨50, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (1286828850399 / 1562500000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (228160103169 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_51 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82323205758079 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140802515967 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨51, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82323205758079 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140802515967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_52 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20572347127739 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281609038411 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨52, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20572347127739 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281609038411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_53 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (16451118931153 / 20000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281613048549 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨53, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (16451118931153 / 20000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281613048549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_54 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (16444364832849 / 20000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456323411913 / 20000000000000 : ℝ))
      (E := (cell12465 ⟨54, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (16444364832849 / 20000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456323411913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_55 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (3287523080331 / 4000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570405267117 / 25000000000000 : ℝ))
      (E := (cell12465 ⟨55, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (3287523080331 / 4000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570405267117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_56 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82154353159879 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281625072053 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨56, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82154353159879 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281625072053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_57 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82120652591217 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (228162906691 / 10000000000000 : ℝ))
      (E := (cell12465 ⟨57, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82120652591217 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (228162906691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_58 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20521743818647 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (114081652471 / 5000000000000 : ℝ))
      (E := (cell12465 ⟨58, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20521743818647 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (114081652471 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_59 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82053321182433 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140818537463 / 50000000000000 : ℝ))
      (E := (cell12465 ⟨59, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82053321182433 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (1140818537463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12466_40 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (16539348937653 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140714174233 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨40, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (16539348937653 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140714174233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_41 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (20665667133719 / 25000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570358087317 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨41, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (20665667133719 / 25000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570358087317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_42 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82628616093433 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570359092769 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨42, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82628616093433 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570359092769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_43 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (5162161708379 / 6250000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (57036008867 / 2500000000000 : ℝ))
      (E := (cell12466 ⟨43, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (5162161708379 / 6250000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (57036008867 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_44 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (10320072778381 / 12500000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (142590272387 / 6250000000000 : ℝ))
      (E := (cell12466 ⟨44, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (10320072778381 / 12500000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (142590272387 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_45 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (16505320148563 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281448321913 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨45, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (16505320148563 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281448321913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_46 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82492642851941 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (456290472487 / 20000000000000 : ℝ))
      (E := (cell12466 ⟨46, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82492642851941 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (456290472487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_47 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (16491741705031 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281456360759 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨47, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (16491741705031 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281456360759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_48 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (5151549858333 / 6250000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (91258414969 / 4000000000000 : ℝ))
      (E := (cell12466 ⟨48, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (5151549858333 / 6250000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (91258414969 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_49 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (41195455223741 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140732171087 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨49, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (41195455223741 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140732171087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_50 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82357046638783 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281468321563 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨50, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82357046638783 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281468321563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_51 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (4116160313927 / 5000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570368092307 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨51, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (4116160313927 / 5000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570368092307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_52 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (2571543416819 / 3125000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140738182433 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨52, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (2571543416819 / 3125000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140738182433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_53 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (41127797894693 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140740182431 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨53, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (41127797894693 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140740182431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_54 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (20555456400953 / 25000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281484366437 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨54, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (20555456400953 / 25000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281484366437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_55 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82188078753369 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140744183297 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨55, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82188078753369 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140744183297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_56 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82154355210079 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (228149236213 / 10000000000000 : ℝ))
      (E := (cell12466 ⟨56, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82154355210079 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (228149236213 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_57 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82120654946103 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140748174817 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨57, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82120654946103 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140748174817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_58 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82086977933743 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281500384633 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨58, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82086977933743 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281500384633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_59 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (41026662072719 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570376086257 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨59, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (41026662072719 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570376086257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12467_40 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (132314786891 / 160000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281295730457 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨40, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (132314786891 / 160000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281295730457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_41 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82662665964933 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (57032492817 / 2500000000000 : ℝ))
      (E := (cell12467 ⟨41, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82662665964933 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (57032492817 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_42 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82628613834507 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (285162964577 / 12500000000000 : ℝ))
      (E := (cell12467 ⟨42, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82628613834507 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (285162964577 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_43 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (3303783415429 / 4000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281307683053 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨43, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (3303783415429 / 4000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281307683053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_44 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82560580588867 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281311728921 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨44, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82560580588867 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281311728921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_45 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (20631649853591 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (9125262943 / 400000000000 : ℝ))
      (E := (cell12467 ⟨45, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (20631649853591 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (9125262943 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_46 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82492641832793 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281319702399 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨46, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82492641832793 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281319702399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_47 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82458707814881 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281323686397 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨47, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82458707814881 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281323686397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_48 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (16484959466301 / 20000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570331921559 / 25000000000000 : ℝ))
      (E := (cell12467 ⟨48, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (16484959466301 / 20000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570331921559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_49 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82390910353683 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140665850099 / 50000000000000 : ℝ))
      (E := (cell12467 ⟨49, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82390910353683 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140665850099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_50 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82357046852583 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281335726347 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨50, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82357046852583 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281335726347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_51 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (20580801699879 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (8911483217 / 390625000000 : ℝ))
      (E := (cell12467 ⟨51, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (20580801699879 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (8911483217 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_52 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41144695082969 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281343688389 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨52, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41144695082969 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281343688389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_53 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41127798461723 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456269547463 / 20000000000000 : ℝ))
      (E := (cell12467 ⟨53, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41127798461723 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456269547463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_54 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41110913521891 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570337932377 / 25000000000000 : ℝ))
      (E := (cell12467 ⟨54, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41110913521891 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570337932377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_55 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (20547020124707 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281355720981 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨55, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (20547020124707 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281355720981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_56 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41077178630303 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281359708531 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨56, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41077178630303 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281359708531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_57 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (513254108133 / 625000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281363747867 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨57, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (513254108133 / 625000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281363747867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_58 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (1641739611863 / 2000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281367717147 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨58, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (1641739611863 / 2000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281367717147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_59 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82053327108657 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570342932703 / 25000000000000 : ℝ))
      (E := (cell12467 ⟨59, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82053327108657 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570342932703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12468_40 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (4134836946321 / 5000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281163109049 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨40, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (4134836946321 / 5000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281163109049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_41 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82662663395887 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (57029178287 / 2500000000000 : ℝ))
      (E := (cell12468 ⟨41, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82662663395887 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (57029178287 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_42 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82628611576439 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281171117607 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨42, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82628611576439 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281171117607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_43 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41297291719103 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456235025147 / 20000000000000 : ℝ))
      (E := (cell12468 ⟨43, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41297291719103 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456235025147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_44 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (20640144737867 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281179096409 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨44, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (20640144737867 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281179096409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_45 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (5037023809 / 6103515625 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140591573193 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨45, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (5037023809 / 6103515625 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140591573193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_46 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82492640814349 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281187098067 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨46, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82492640814349 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281187098067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_47 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (20614676776319 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (71287222709 / 3125000000000 : ℝ))
      (E := (cell12468 ⟨47, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (20614676776319 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (71287222709 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_48 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (8242479693031 / 10000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570298778247 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨48, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (8242479693031 / 10000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570298778247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_49 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (3295636410419 / 4000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (17821868079 / 781250000000 : ℝ))
      (E := (cell12468 ⟨49, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (3295636410419 / 4000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (17821868079 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_50 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82357047066937 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281203128123 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨50, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82357047066937 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281203128123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_51 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82323207321009 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140603576437 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨51, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82323207321009 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140603576437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_52 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41144695497073 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570302781749 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨52, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41144695497073 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570302781749 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_53 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82255598057947 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (3649944171 / 160000000000 : ℝ))
      (E := (cell12468 ⟨53, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82255598057947 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (3649944171 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_54 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (16444365696831 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (114060957439 / 5000000000000 : ℝ))
      (E := (cell12468 ⟨54, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (16444365696831 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (114060957439 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_55 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82188082244651 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (142576445727 / 6250000000000 : ℝ))
      (E := (cell12468 ⟨55, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82188082244651 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (142576445727 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_56 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (4107717965573 / 5000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281227111257 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨56, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (4107717965573 / 5000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281227111257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_57 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (16424131931349 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140615571683 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨57, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (16424131931349 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140615571683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_58 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82086983252809 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140617582629 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨58, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82086983252809 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140617582629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_59 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82053330072091 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (142577444621 / 6250000000000 : ℝ))
      (E := (cell12468 ⟨59, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82053330072091 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (142577444621 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12469_40 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82696736046901 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281030601693 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨40, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82696736046901 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281030601693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_41 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41331330413869 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281034605671 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨41, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41331330413869 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281034605671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_42 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82628609319231 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (45620771481 / 2000000000000 : ℝ))
      (E := (cell12469 ⟨42, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82628609319231 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (45620771481 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_43 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (20648645372877 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281042565137 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨43, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (20648645372877 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281042565137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_44 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82560577314851 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140523289147 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨44, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82560577314851 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140523289147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_45 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (20631649189923 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281050612663 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨45, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (20631649189923 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281050612663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_46 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (20623159949153 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281054608303 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨46, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (20623159949153 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281054608303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_47 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82458706396337 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140529311373 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨47, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82458706396337 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140529311373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_48 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (16484959305949 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281062595569 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨48, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (16484959305949 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281062595569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_49 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41195455083929 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281066583917 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨49, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41195455083929 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281066583917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_50 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (20589261820461 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140535292927 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨50, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (20589261820461 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140535292927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_51 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (10290400980377 / 12500000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (228107459923 / 10000000000000 : ℝ))
      (E := (cell12469 ⟨51, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (10290400980377 / 12500000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (228107459923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_52 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82289391822831 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140539310841 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨52, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82289391822831 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140539310841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_53 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (10281949899111 / 12500000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140541295803 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨53, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (10281949899111 / 12500000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140541295803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_54 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82221829924929 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (4455247313 / 195312500000 : ℝ))
      (E := (cell12469 ⟨54, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82221829924929 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (4455247313 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_55 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82188083990839 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281090598549 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨55, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82188083990839 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281090598549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_56 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82154361362641 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (570273657353 / 25000000000000 : ℝ))
      (E := (cell12469 ⟨56, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82154361362641 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (570273657353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_57 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (6569652961 / 8000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281098595253 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨57, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (6569652961 / 8000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281098595253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_58 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82086985912719 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140551305337 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨58, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82086985912719 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140551305337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_59 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82053333035739 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456221322549 / 20000000000000 : ℝ))
      (E := (cell12469 ⟨59, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82053333035739 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456221322549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12470_40 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (20674183292079 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (114044904547 / 5000000000000 : ℝ))
      (E := (cell12470 ⟨40, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (20674183292079 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (114044904547 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_41 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (41331329130243 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570225533813 / 25000000000000 : ℝ))
      (E := (cell12470 ⟨41, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (41331329130243 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570225533813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_42 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (516428794143 / 625000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280906085947 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨42, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (516428794143 / 625000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280906085947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_43 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82594579545629 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280910118851 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨43, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82594579545629 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280910118851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_44 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (10320071959877 / 12500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280914115757 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨44, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (10320071959877 / 12500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280914115757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_45 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (80592378353 / 97656250000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (114045906729 / 5000000000000 : ℝ))
      (E := (cell12470 ⟨45, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (80592378353 / 97656250000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (114045906729 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_46 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82492638779579 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280922115379 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨46, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82492638779579 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280922115379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_47 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (41229352844033 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280926115681 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨47, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (41229352844033 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280926115681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_48 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82424796129809 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (114046506699 / 5000000000000 : ℝ))
      (E := (cell12470 ⟨48, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82424796129809 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (114046506699 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_49 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82390910075833 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140467054807 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨49, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82390910075833 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140467054807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_50 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (16471409499461 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140469049769 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨50, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (16471409499461 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140469049769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_51 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82323208365539 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280942101601 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨51, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82323208365539 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280942101601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_52 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82289392651993 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280946113441 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨52, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82289392651993 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280946113441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_53 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (20563900082067 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1781992291 / 78125000000 : ℝ))
      (E := (cell12470 ⟨53, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (20563900082067 / 25000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1781992291 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_54 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (16444366273221 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140477048441 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨54, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (16444366273221 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140477048441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_55 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82188085737391 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280958121731 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨55, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82188085737391 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280958121731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_56 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82154363414149 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140481072397 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨56, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82154363414149 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140481072397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_57 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (2566270761517 / 3125000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280966103529 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨57, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (2566270761517 / 3125000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280966103529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_58 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82086988572881 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280970112541 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨58, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82086988572881 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280970112541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_59 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82053335999601 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (71280440903 / 3125000000000 : ℝ))
      (E := (cell12470 ⟨59, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82053335999601 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (71280440903 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12471_40 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41348365145333 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280765694241 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨40, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41348365145333 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280765694241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_41 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (8266265569413 / 10000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280769661477 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨41, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (8266265569413 / 10000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280769661477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_42 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82628604807387 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280773712071 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨42, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82628604807387 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280773712071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_43 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (8259457760057 / 10000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280777669287 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨43, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (8259457760057 / 10000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280777669287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_44 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41280287021981 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280781708801 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨44, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41280287021981 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280781708801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_45 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (16505318821599 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280785712141 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨45, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (16505318821599 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280785712141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_46 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82492637763251 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280789678161 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨46, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82492637763251 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280789678161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_47 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82458704980461 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140396832193 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨47, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82458704980461 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140396832193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_48 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41212397865251 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (570199417327 / 25000000000000 : ℝ))
      (E := (cell12471 ⟨48, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41212397865251 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (570199417327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_49 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41195454992199 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456160338241 / 20000000000000 : ℝ))
      (E := (cell12471 ⟨49, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41195454992199 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456160338241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_50 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41178523856659 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280805669179 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨50, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41178523856659 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280805669179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_51 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82323208888577 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (91232388759 / 4000000000000 : ℝ))
      (E := (cell12471 ⟨51, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82323208888577 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (91232388759 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_52 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82289393481633 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140406860143 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨52, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82289393481633 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140406860143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_53 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82255601464087 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140408835233 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨53, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82255601464087 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140408835233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_54 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (20555458201921 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456164336953 / 20000000000000 : ℝ))
      (E := (cell12471 ⟨54, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (20555458201921 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456164336953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_55 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82188087484307 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280825701181 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨55, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82188087484307 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280825701181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_56 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82154365465983 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456165943301 / 20000000000000 : ℝ))
      (E := (cell12471 ⟨56, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82154365465983 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456165943301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_57 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82120666724877 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140416863661 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨57, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82120666724877 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140416863661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_58 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (16417398246659 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280837730009 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨58, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (16417398246659 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280837730009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_59 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82053338963677 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456168344147 / 20000000000000 : ℝ))
      (E := (cell12471 ⟨59, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82053338963677 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456168344147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12472_40 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82696727413951 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280633294147 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨40, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82696727413951 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280633294147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_41 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (8266265312867 / 10000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280637301843 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨41, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (8266265312867 / 10000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280637301843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_42 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (5164287659547 / 6250000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (14254008343 / 625000000000 : ℝ))
      (E := (cell12472 ⟨42, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (5164287659547 / 6250000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (14254008343 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_43 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82594575656331 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140322667019 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨43, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82594575656331 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140322667019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_44 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82560572409689 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280649298609 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨44, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82560572409689 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280649298609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_45 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82526592783261 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (285081660813 / 12500000000000 : ℝ))
      (E := (cell12472 ⟨45, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82526592783261 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (285081660813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_46 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (20623159186907 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (45613145933 / 2000000000000 : ℝ))
      (E := (cell12472 ⟨46, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (20623159186907 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (45613145933 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_47 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82458704273523 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280661327749 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨47, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82458704273523 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280661327749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_48 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (5151549708239 / 6250000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140332659691 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨48, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (5151549708239 / 6250000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140332659691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_49 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (41195454946777 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280669328691 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨49, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (41195454946777 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280669328691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_50 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (20589261982471 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280673294777 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨50, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (20589261982471 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280673294777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_51 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (8232320941213 / 10000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (456135466677 / 20000000000000 : ℝ))
      (E := (cell12472 ⟨51, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (8232320941213 / 10000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (456135466677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_52 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (329157577247 / 400000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280681324207 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨52, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (329157577247 / 400000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280681324207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_53 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (41127801300173 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280685323627 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨53, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (41127801300173 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280685323627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_54 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82221834249663 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280689328857 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨54, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82221834249663 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280689328857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_55 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82188089231587 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280693336899 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨55, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82188089231587 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280693336899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_56 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82154367518143 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280697344547 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨56, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82154367518143 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280697344547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_57 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82120669081499 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280701348383 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨57, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82120669081499 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280701348383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_58 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82086993893959 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (142544084049 / 6250000000000 : ℝ))
      (E := (cell12472 ⟨58, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82086993893959 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (142544084049 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_59 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (2564166935249 / 3125000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280709329917 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨59, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (2564166935249 / 3125000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280709329917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12473_40 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (8269672453817 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280501008109 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨40, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (8269672453817 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280501008109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_41 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (41331325282053 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570126249401 / 25000000000000 : ℝ))
      (E := (cell12473 ⟨41, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (41331325282053 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570126249401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_42 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (3305144011959 / 4000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (285063626643 / 12500000000000 : ℝ))
      (E := (cell12473 ⟨42, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (3305144011959 / 4000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (285063626643 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_43 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (8259457371291 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280512995513 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨43, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (8259457371291 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280512995513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_44 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82560570776197 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280517002817 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨44, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82560570776197 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280517002817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_45 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82526591459269 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456104195071 / 20000000000000 : ℝ))
      (E := (cell12473 ⟨45, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82526591459269 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456104195071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_46 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (8249263573271 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456104994169 / 20000000000000 : ℝ))
      (E := (cell12473 ⟨46, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (8249263573271 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456104994169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_47 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20614675891813 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280528987993 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨47, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20614675891813 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280528987993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_48 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82424794933773 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (285066620797 / 12500000000000 : ℝ))
      (E := (cell12473 ⟨48, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82424794933773 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (285066620797 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_49 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (823909098033 / 1000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456107392627 / 20000000000000 : ℝ))
      (E := (cell12473 ⟨49, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (823909098033 / 1000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456107392627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_50 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82357048147003 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570135244083 / 25000000000000 : ℝ))
      (E := (cell12473 ⟨50, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82357048147003 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570135244083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_51 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82323209936197 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456109000763 / 20000000000000 : ℝ))
      (E := (cell12473 ⟨51, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82323209936197 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456109000763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_52 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82289395142343 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228054898421 / 10000000000000 : ℝ))
      (E := (cell12473 ⟨52, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82289395142343 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228054898421 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_53 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20563900934261 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280552973901 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨53, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20563900934261 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280552973901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_54 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20555458923011 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (22805569701 / 1000000000000 : ℝ))
      (E := (cell12473 ⟨54, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20555458923011 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (22805569701 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_55 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82188090979231 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280560969807 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨55, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82188090979231 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280560969807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_56 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (8215436957063 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280565028919 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨56, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (8215436957063 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280565028919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_57 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (8212067143841 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570142256459 / 25000000000000 : ℝ))
      (E := (cell12473 ⟨57, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (8212067143841 / 10000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570142256459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_58 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (656695972439 / 800000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280573016013 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨58, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (656695972439 / 800000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280573016013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_59 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82053344892471 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280576995617 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨59, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82053344892471 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280576995617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12474_40 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82696721663323 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280368718679 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨40, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82696721663323 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280368718679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_41 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82662648000437 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280372690011 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨41, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82662648000437 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280372690011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_42 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41314299023027 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (71261771503 / 3125000000000 : ℝ))
      (E := (cell12474 ⟨42, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41314299023027 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (71261771503 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_43 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (20648642942577 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (228038071251 / 10000000000000 : ℝ))
      (E := (cell12474 ⟨43, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (20648642942577 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (228038071251 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_44 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (16512113828697 / 20000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280384703791 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨44, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (16512113828697 / 20000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280384703791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_45 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (4126329506801 / 5000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570097179963 / 25000000000000 : ℝ))
      (E := (cell12474 ⟨45, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (4126329506801 / 5000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570097179963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_46 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (2577894834953 / 3125000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (9121570803 / 400000000000 : ℝ))
      (E := (cell12474 ⟨46, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (2577894834953 / 3125000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (9121570803 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_47 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82458702861647 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (285049588001 / 12500000000000 : ℝ))
      (E := (cell12474 ⟨47, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82458702861647 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (285049588001 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_48 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82424794536351 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280400728117 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨48, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82424794536351 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280400728117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_49 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (20597727428409 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280404712413 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨49, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (20597727428409 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280404712413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_50 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82357048364673 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280408713847 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨50, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82357048364673 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280408713847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_51 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82323210460779 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140206365133 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨51, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82323210460779 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140206365133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_52 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41144697986707 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (285052087537 / 12500000000000 : ℝ))
      (E := (cell12474 ⟨52, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41144697986707 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (285052087537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_53 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82255604874181 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280420739351 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨53, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82255604874181 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280420739351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_54 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82221837134827 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (456084945321 / 20000000000000 : ℝ))
      (E := (cell12474 ⟨54, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82221837134827 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (456084945321 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_55 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41094046363619 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (456085743613 / 20000000000000 : ℝ))
      (E := (cell12474 ⟨55, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41094046363619 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (456085743613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_56 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82154371623443 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280432710521 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨56, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82154371623443 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280432710521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_57 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82120673795609 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140218350279 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨57, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82120673795609 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140218350279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_58 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41043499608021 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280440743699 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨58, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41043499608021 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280440743699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_59 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82053347857189 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140222358917 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨59, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82053347857189 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140222358917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

end BstLean.Part268
