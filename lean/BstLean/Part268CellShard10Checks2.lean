import BstLean.Part268CellShard10Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12600_40 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41348183404893 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132042074347 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨40, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41348183404893 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132042074347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_41 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (16532466410137 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (283011016187 / 12500000000000 : ℝ))
      (E := (cell12600 ⟨41, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (16532466410137 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (283011016187 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_42 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82628320946331 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132046084133 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨42, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82628320946331 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132046084133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_43 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82594333466959 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132048073399 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨43, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82594333466959 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132048073399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_44 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82560369582949 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132050061489 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨44, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82560369582949 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132050061489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_45 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41263214632417 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264104154569 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨45, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41263214632417 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264104154569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_46 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82492512483293 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264108122573 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨46, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82492512483293 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264108122573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_47 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (16491723841831 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (566028035799 / 25000000000000 : ℝ))
      (E := (cell12600 ⟨47, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (16491723841831 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (566028035799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_48 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41212374706697 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132058077921 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨48, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41212374706697 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132058077921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_49 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (8239090306713 / 10000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (452824031711 / 20000000000000 : ℝ))
      (E := (cell12600 ⟨49, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (8239090306713 / 10000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (452824031711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_50 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82357080141627 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264124149167 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨50, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82357080141627 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264124149167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_51 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82323280608297 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264128184287 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨51, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82323280608297 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264128184287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_52 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (8228950443869 / 10000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132066071677 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨52, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (8228950443869 / 10000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132066071677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_53 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41127875802251 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264136200621 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨53, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41127875802251 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264136200621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_54 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82222022077569 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264140176013 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨54, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82222022077569 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264140176013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_55 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (8218831582987 / 10000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264144184411 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨55, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (8218831582987 / 10000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264144184411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_56 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82154632833521 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132074081669 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨56, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82154632833521 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132074081669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_57 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82120973060779 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (70754755259 / 3125000000000 : ℝ))
      (E := (cell12600 ⟨57, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82120973060779 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (70754755259 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_58 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (2052183412101 / 2500000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264156195479 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨58, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (2052183412101 / 2500000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264156195479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_59 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (20513430768959 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (113208009087 / 5000000000000 : ℝ))
      (E := (cell12600 ⟨59, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (20513430768959 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (113208009087 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12601_40 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (20674091012823 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263957662161 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨40, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (20674091012823 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263957662161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_41 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41331164799277 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263961690987 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨41, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41331164799277 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263961690987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_42 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (4131415940007 / 5000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263965660957 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨42, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (4131415940007 / 5000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263965660957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_43 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (16518866325257 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263969688957 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨43, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (16518866325257 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263969688957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_44 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82560368047371 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (45279474307 / 2000000000000 : ℝ))
      (E := (cell12601 ⟨44, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82560368047371 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (45279474307 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_45 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82526428033931 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263977680187 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨45, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82526428033931 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263977680187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_46 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41246255778323 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131990849921 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨46, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41246255778323 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131990849921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_47 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (10307327323293 / 12500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131992856979 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨47, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (10307327323293 / 12500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131992856979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_48 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41212374547 / 50000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (282998715099 / 12500000000000 : ℝ))
      (E := (cell12601 ⟨48, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41212374547 / 50000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (282998715099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_49 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (16478180610147 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263993718387 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨49, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (16478180610147 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263993718387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_50 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (16471416085563 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263997704573 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨50, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (16471416085563 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263997704573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_51 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82323281196651 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2264001735961 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨51, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82323281196651 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2264001735961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_52 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41144752664397 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (70750179719 / 3125000000000 : ℝ))
      (E := (cell12601 ⟨52, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41144752664397 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (70750179719 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_53 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41127876397971 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1132004873453 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨53, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41127876397971 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1132004873453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_54 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82222023569931 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1132006860319 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨54, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82222023569931 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1132006860319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_55 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82188317622739 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (566004432017 / 25000000000000 : ℝ))
      (E := (cell12601 ⟨55, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82188317622739 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (566004432017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_56 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41077317463243 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (226402176583 / 10000000000000 : ℝ))
      (E := (cell12601 ⟨56, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41077317463243 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (226402176583 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_57 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82120975453427 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (566006442803 / 25000000000000 : ℝ))
      (E := (cell12601 ⟨57, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82120975453427 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (566006442803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_58 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (2052183479399 / 2500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2264029740363 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨58, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (2052183479399 / 2500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2264029740363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_59 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82053726066617 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2264033728409 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨59, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82053726066617 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2264033728409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12602_40 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82696361293697 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263831289839 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨40, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82696361293697 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263831289839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_41 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (20665581786821 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263835308013 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨41, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (20665581786821 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263835308013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_42 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82628316654773 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263839268029 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨42, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82628316654773 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263839268029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_43 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41297164893199 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131921643387 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨43, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41297164893199 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131921643387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_44 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82560366512543 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (226384730461 / 10000000000000 : ℝ))
      (E := (cell12602 ⟨44, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82560366512543 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (226384730461 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_45 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82526426803741 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (452770252317 / 20000000000000 : ℝ))
      (E := (cell12602 ⟨45, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82526426803741 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (452770252317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_46 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41246255315337 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565963818519 / 25000000000000 : ℝ))
      (E := (cell12602 ⟨46, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41246255315337 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565963818519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_47 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (8245861796417 / 10000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565964820431 / 25000000000000 : ℝ))
      (E := (cell12602 ⟨47, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (8245861796417 / 10000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565964820431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_48 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82424748775207 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263863282783 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨48, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82424748775207 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263863282783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_49 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10298862879363 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131933637649 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨49, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10298862879363 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131933637649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_50 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (8235708071453 / 10000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565967829017 / 25000000000000 : ℝ))
      (E := (cell12602 ⟨50, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (8235708071453 / 10000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565967829017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_51 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (16464656357099 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263875284789 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨51, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (16464656357099 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263875284789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_52 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10286188277419 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263879296833 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨52, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10286188277419 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263879296833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_53 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41127876993899 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (113194164521 / 5000000000000 : ℝ))
      (E := (cell12602 ⟨53, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41127876993899 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (113194164521 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_54 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (5138876566417 / 6250000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131943660799 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨54, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (5138876566417 / 6250000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131943660799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_55 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (5136769963497 / 6250000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (56597283203 / 2500000000000 : ℝ))
      (E := (cell12602 ⟨55, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (5136769963497 / 6250000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (56597283203 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_56 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82154637019757 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (45277906131 / 2000000000000 : ℝ))
      (E := (cell12602 ⟨56, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82154637019757 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (45277906131 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_57 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (16424195569269 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263899312379 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨57, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (16424195569269 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263899312379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_58 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82087341868113 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (90556133673 / 4000000000000 : ℝ))
      (E := (cell12602 ⟨58, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82087341868113 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (90556133673 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_59 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (16410745811519 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565976832929 / 25000000000000 : ℝ))
      (E := (cell12602 ⟨59, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (16410745811519 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565976832929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12603_40 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82696358537 / 100000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131852457127 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨40, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82696358537 / 100000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131852457127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_41 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (26451943903 / 32000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131854460907 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨41, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (26451943903 / 32000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131854460907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_42 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (8262831451023 / 10000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263712930699 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨42, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (8262831451023 / 10000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263712930699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_43 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82594327947297 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565929235063 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨43, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82594327947297 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565929235063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_44 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (2580011405577 / 3125000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263720890759 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨44, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (2580011405577 / 3125000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263720890759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_45 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (41263212787131 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (141482806173 / 6250000000000 : ℝ))
      (E := (cell12603 ⟨45, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (41263212787131 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (141482806173 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_46 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (2577890928293 / 3125000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565932226039 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨46, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (2577890928293 / 3125000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565932226039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_47 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (41229308671317 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452746581079 / 20000000000000 : ℝ))
      (E := (cell12603 ⟨47, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (41229308671317 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452746581079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_48 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (41212374228507 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565934239917 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨48, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (41212374228507 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565934239917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_49 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82390903019637 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131870473593 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨49, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82390903019637 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131870473593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_50 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (20589270250443 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263744924681 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨50, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (20589270250443 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263744924681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_51 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82323282374829 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452749789753 / 20000000000000 : ℝ))
      (E := (cell12603 ⟨51, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82323282374829 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452749789753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_52 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82289507110363 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263752957891 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨52, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82289507110363 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263752957891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_53 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82255755180071 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565939237313 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨53, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82255755180071 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565939237313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_54 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82222026555793 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263760978893 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨54, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82222026555793 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263760978893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_55 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (20547080302377 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263764984569 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨55, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (20547080302377 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263764984569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_56 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (16430927822667 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263768962841 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨56, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (16430927822667 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263768962841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_57 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82120980239533 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263772969201 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨57, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82120980239533 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263772969201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_58 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (164174689121 / 200000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131888499933 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨58, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (164174689121 / 200000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131888499933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_59 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (8205373204877 / 10000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263780991663 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨59, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (8205373204877 / 10000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263780991663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12604_40 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41348177890601 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (70736831067 / 3125000000000 : ℝ))
      (E := (cell12604 ⟨40, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41348177890601 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (70736831067 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_41 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82662322247327 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263582591153 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨41, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82662322247327 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263582591153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_42 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82628312366509 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (452717318037 / 20000000000000 : ℝ))
      (E := (cell12604 ⟨42, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82628312366509 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (452717318037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_43 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82594326108983 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263590590581 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨43, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82594326108983 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263590590581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_44 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82560363445133 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263594591463 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨44, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82560363445133 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263594591463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_45 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (10315803043187 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131799295867 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨45, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (10315803043187 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131799295867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_46 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82492508780753 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263602590081 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨46, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82492508780753 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263602590081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_47 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (10307327090217 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263606584973 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨47, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (10307327090217 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263606584973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_48 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41212374069711 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131805316797 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨48, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41212374069711 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131805316797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_49 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41195451502467 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (452722923231 / 20000000000000 : ℝ))
      (E := (cell12604 ⟨49, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41195451502467 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (452722923231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_50 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (4117854064477 / 5000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131809294693 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨50, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (4117854064477 / 5000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131809294693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_51 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (20580820741163 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131811304949 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨51, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (20580820741163 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131811304949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_52 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82289508001827 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263626616143 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨52, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82289508001827 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263626616143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_53 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (2056393909319 / 2500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131815302657 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨53, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (2056393909319 / 2500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131815302657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_54 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41111014024647 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263634633457 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨54, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41111014024647 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263634633457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_55 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41094161501703 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (565909659581 / 25000000000000 : ℝ))
      (E := (cell12604 ⟨55, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41094161501703 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (565909659581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_56 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82154641207219 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (565910654119 / 25000000000000 : ℝ))
      (E := (cell12604 ⟨56, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82154641207219 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (565910654119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_57 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (8212098263299 / 10000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (452729324681 / 20000000000000 : ℝ))
      (E := (cell12604 ⟨57, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (8212098263299 / 10000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (452729324681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_58 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82087347253119 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263650655327 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨58, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82087347253119 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263650655327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_59 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (82053735040141 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263654649067 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨59, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (82053735040141 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263654649067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12605_40 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82696353026301 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565863067693 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨40, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82696353026301 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565863067693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_41 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (1033278997483 / 1250000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565864079007 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨41, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (1033278997483 / 1250000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565864079007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_42 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20657077555903 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263460305269 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨42, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20657077555903 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263460305269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_43 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41297162135727 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565866074143 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨43, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41297162135727 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565866074143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_44 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (10320045239069 / 12500000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263468289057 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨44, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (10320045239069 / 12500000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263468289057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_45 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (128947536121 / 156250000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263472281629 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨45, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (128947536121 / 156250000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263472281629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_46 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20623126964201 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565869082963 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨46, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20623126964201 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565869082963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_47 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (3298344644059 / 4000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263480320459 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨47, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (3298344644059 / 4000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263480320459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_48 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (8242474782243 / 10000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565871076141 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨48, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (8242474782243 / 10000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565871076141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_49 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82390902990793 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (452697668231 / 20000000000000 : ℝ))
      (E := (cell12605 ⟨49, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82390902990793 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (452697668231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_50 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41178540788917 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131746155091 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨50, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41178540788917 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131746155091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_51 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (16464656710993 / 20000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263496327183 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨51, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (16464656710993 / 20000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263496327183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_52 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82289508893743 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263500330609 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨52, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82289508893743 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263500330609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_53 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (16451151513173 / 20000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565876079413 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨53, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (16451151513173 / 20000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565876079413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_54 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82222029543173 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131754172179 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨54, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82222029543173 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131754172179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_55 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82188324797647 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263512348477 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨55, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82188324797647 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263512348477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_56 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (2567332603169 / 3125000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (226351632657 / 10000000000000 : ℝ))
      (E := (cell12605 ⟨56, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (2567332603169 / 3125000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (226351632657 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_57 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82120985026717 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (141470020883 / 6250000000000 : ℝ))
      (E := (cell12605 ⟨57, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82120985026717 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (141470020883 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_58 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20521837486493 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263524367367 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨58, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20521837486493 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263524367367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_59 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82053738031709 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (282941045389 / 12500000000000 : ℝ))
      (E := (cell12605 ⟨59, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82053738031709 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (282941045389 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12606_40 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41348175136149 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263326061617 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨40, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41348175136149 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263326061617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_41 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (82662317350813 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131665018841 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨41, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (82662317350813 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131665018841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_42 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41314154040769 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452666815191 / 20000000000000 : ℝ))
      (E := (cell12606 ⟨42, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41314154040769 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452666815191 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_43 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (82594322434711 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131669029113 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨43, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (82594322434711 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131669029113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_44 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41280180190359 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263342042377 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨44, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41280180190359 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263342042377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_45 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (5157901368131 / 6250000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263346086167 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨45, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (5157901368131 / 6250000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263346086167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_46 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (8249250693353 / 10000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263350070591 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨46, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (8249250693353 / 10000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263350070591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_47 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (82458615481851 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (282919256619 / 12500000000000 : ℝ))
      (E := (cell12606 ⟨47, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (82458615481851 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (282919256619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_48 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41212373753019 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263358090431 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨48, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41212373753019 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263358090431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_49 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (1287357859019 / 1562500000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263362063237 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨49, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (1287357859019 / 1562500000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263362063237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_50 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (16471416373331 / 20000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (70730190221 / 3125000000000 : ℝ))
      (E := (cell12606 ⟨50, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (16471416373331 / 20000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (70730190221 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_51 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (10290410518221 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263370100623 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨51, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (10290410518221 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263370100623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_52 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (160721698801 / 195312500000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (565843525323 / 25000000000000 : ℝ))
      (E := (cell12606 ⟨52, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (160721698801 / 195312500000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (565843525323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_53 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41127879379693 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (565844521567 / 25000000000000 : ℝ))
      (E := (cell12606 ⟨53, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41127879379693 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (565844521567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_54 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (10277753879679 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263382111597 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨54, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (10277753879679 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263382111597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_55 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (82188326592231 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (565846528757 / 25000000000000 : ℝ))
      (E := (cell12606 ⟨55, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (82188326592231 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (565846528757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_56 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (1283666334311 / 1562500000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (565847523281 / 25000000000000 : ℝ))
      (E := (cell12606 ⟨56, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (1283666334311 / 1562500000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (565847523281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_57 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (82120987420713 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263394101373 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨57, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (82120987420713 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263394101373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_58 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41043676319529 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263398135989 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨58, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41043676319529 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263398135989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_59 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41026870511737 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263402133799 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨59, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41026870511737 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263402133799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12607_40 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (10337043439899 / 12500000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263199849201 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨40, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (10337043439899 / 12500000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263199849201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_41 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (41331157451923 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (18105630519 / 800000000000 : ℝ))
      (E := (cell12607 ⟨41, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (41331157451923 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (18105630519 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_42 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82628305940287 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (17681311277 / 781250000000 : ℝ))
      (E := (cell12607 ⟨42, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82628305940287 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (17681311277 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_43 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82594320598753 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263211875543 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨43, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82594320598753 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263211875543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_44 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82560358849633 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131607925711 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨44, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82560358849633 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131607925711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_45 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82526420663463 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263219828779 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨45, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82526420663463 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263219828779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_46 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82492506010929 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263223865179 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨46, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82492506010929 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263223865179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_47 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82458614862863 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452645568271 / 20000000000000 : ℝ))
      (E := (cell12607 ⟨47, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82458614862863 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452645568271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_48 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (41212373595123 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131615936671 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨48, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (41212373595123 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131615936671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_49 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (41195451482101 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263235841351 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨49, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (41195451482101 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263235841351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_50 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (41178541078001 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263239861081 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨50, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (41178541078001 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263239861081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_51 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82323284737059 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131621935611 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨51, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82323284737059 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131621935611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_52 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82289510678933 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (226324786917 / 10000000000000 : ℝ))
      (E := (cell12607 ⟨52, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82289510678933 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (226324786917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_53 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82255759953323 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (56581297779 / 2500000000000 : ℝ))
      (E := (cell12607 ⟨53, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82255759953323 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (56581297779 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_54 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (8222203253207 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131627938053 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨54, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (8222203253207 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131627938053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_55 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (20547082096789 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263259878889 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨55, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (20547082096789 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263259878889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_56 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (41077323745353 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131631958069 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨56, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (41077323745353 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131631958069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_57 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82120989814979 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131633962569 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨57, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82120989814979 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131633962569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_58 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (10260919416547 / 12500000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263271902033 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨58, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (10260919416547 / 12500000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263271902033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_59 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (16410748803087 / 20000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452655180389 / 20000000000000 : ℝ))
      (E := (cell12607 ⟨59, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (16410748803087 / 20000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452655180389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12608_40 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (10337043095873 / 12500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282884211533 / 12500000000000 : ℝ))
      (E := (cell12608 ⟨40, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (10337043095873 / 12500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282884211533 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_41 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41331156228869 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263077706373 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨41, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41331156228869 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263077706373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_42 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41314151899929 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263081666561 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨42, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41314151899929 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263081666561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_43 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (82594318763581 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565771422429 / 25000000000000 : ℝ))
      (E := (cell12608 ⟨43, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (82594318763581 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565771422429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_44 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (645002791557 / 781250000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (28288620717 / 1250000000000 : ℝ))
      (E := (cell12608 ⟨44, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (645002791557 / 781250000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (28288620717 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_45 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (82526419437541 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452618737207 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨45, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (82526419437541 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452618737207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_46 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41246252544501 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (70721803613 / 3125000000000 : ℝ))
      (E := (cell12608 ⟨46, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41246252544501 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (70721803613 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_47 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (2576831695141 / 3125000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565775421417 / 25000000000000 : ℝ))
      (E := (cell12608 ⟨47, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (2576831695141 / 3125000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565775421417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_48 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (82424746875053 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131552856113 / 50000000000000 : ℝ))
      (E := (cell12608 ⟨48, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (82424746875053 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131552856113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_49 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (329563611807 / 400000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263109675499 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨49, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (329563611807 / 400000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263109675499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_50 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41178541222937 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263113691187 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨50, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41178541222937 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263113691187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_51 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (2058082133221 / 2500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282889712247 / 12500000000000 : ℝ))
      (E := (cell12608 ⟨51, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (2058082133221 / 2500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282889712247 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_52 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41144755786103 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131560846633 / 50000000000000 : ℝ))
      (E := (cell12608 ⟨52, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41144755786103 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131560846633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_53 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41127880573837 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282890716661 / 12500000000000 : ℝ))
      (E := (cell12608 ⟨53, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41127880573837 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282890716661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_54 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41111017013543 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452625939391 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨54, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41111017013543 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452625939391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_55 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (10273541272803 / 12500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (45262673983 / 2000000000000 : ℝ))
      (E := (cell12608 ⟨55, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (10273541272803 / 12500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (45262673983 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_56 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (82154649585813 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263137736499 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨56, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (82154649585813 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263137736499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_57 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (82120992209513 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263141746289 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨57, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (82120992209513 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263141746289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_58 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (82087358025927 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263145724659 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨58, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (82087358025927 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263145724659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_59 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (10256718375949 / 12500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452629945347 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨59, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (10256718375949 / 12500000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452629945347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12609_40 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (10337042751959 / 12500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262947532071 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨40, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (10337042751959 / 12500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262947532071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_41 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (8266231001249 / 10000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262951535889 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨41, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (8266231001249 / 10000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262951535889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_42 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82628301660251 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (282869443159 / 12500000000000 : ℝ))
      (E := (cell12609 ⟨42, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82628301660251 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (282869443159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_43 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82594316929193 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565739889889 / 25000000000000 : ℝ))
      (E := (cell12609 ⟨43, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82594316929193 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565739889889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_44 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41280177894853 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (113148178893 / 5000000000000 : ℝ))
      (E := (cell12609 ⟨44, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41280177894853 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (113148178893 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_45 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82526418212329 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (90518701609 / 4000000000000 : ℝ))
      (E := (cell12609 ⟨45, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82526418212329 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (90518701609 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_46 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (20623126041937 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (90518862521 / 4000000000000 : ℝ))
      (E := (cell12609 ⟨46, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (20623126041937 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (90518862521 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_47 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41229306813399 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452595117179 / 20000000000000 : ℝ))
      (E := (cell12609 ⟨47, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41229306813399 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452595117179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_48 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (4121237328023 / 5000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131489774079 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨48, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (4121237328023 / 5000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131489774079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_49 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82390902939861 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131491782841 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨49, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82390902939861 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131491782841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_50 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (5147317671017 / 6250000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262987577389 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨50, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (5147317671017 / 6250000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262987577389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_51 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82323285921109 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262991580889 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨51, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82323285921109 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262991580889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_52 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (20572378116483 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (113149778679 / 5000000000000 : ℝ))
      (E := (cell12609 ⟨52, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (20572378116483 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (113149778679 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_53 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82255762342441 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (141437475731 / 6250000000000 : ℝ))
      (E := (cell12609 ⟨53, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82255762342441 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (141437475731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_54 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82222035522481 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131501787073 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨54, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82222035522481 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131501787073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_55 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41094165989017 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131503787907 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨55, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41094165989017 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131503787907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_56 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (3286186067249 / 4000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (90520464533 / 4000000000000 : ℝ))
      (E := (cell12609 ⟨56, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (3286186067249 / 4000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (90520464533 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_57 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82120994604317 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2263015623963 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨57, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82120994604317 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2263015623963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_58 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (8208736071971 / 10000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (70719362621 / 3125000000000 : ℝ))
      (E := (cell12609 ⟨58, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (8208736071971 / 10000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (70719362621 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_59 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (16410749999989 / 20000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2263023608171 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨59, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (16410749999989 / 20000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2263023608171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12610_40 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (10337042408157 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131410743049 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨40, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (10337042408157 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131410743049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_41 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82662307568101 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (226282547971 / 10000000000000 : ℝ))
      (E := (cell12610 ⟨41, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82662307568101 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (226282547971 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_42 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (16525659904293 / 20000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262829479587 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨42, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (16525659904293 / 20000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262829479587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_43 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (8259431509559 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131416742531 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨43, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (8259431509559 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131416742531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_44 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (645002767663 / 781250000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262837495253 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨44, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (645002767663 / 781250000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262837495253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_45 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82526416987827 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565710362551 / 25000000000000 : ℝ))
      (E := (cell12610 ⟨45, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82526416987827 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565710362551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_46 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82492503247167 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452569093257 / 20000000000000 : ℝ))
      (E := (cell12610 ⟨46, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82492503247167 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452569093257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_47 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (2061465325243 / 2500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262849483129 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨47, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (2061465325243 / 2500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262849483129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_48 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41212373123233 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262853498989 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨48, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41212373123233 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262853498989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_49 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82390902928533 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262857511901 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨49, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82390902928533 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262857511901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_50 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (16471416605439 / 20000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262861519687 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨50, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (16471416605439 / 20000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262861519687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_51 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82323286513867 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131432759979 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨51, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82323286513867 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131432759979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_52 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82289513360109 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262869510113 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨52, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82289513360109 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262869510113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_53 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (10281970442203 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131436743669 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨53, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (10281970442203 / 12500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131436743669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_54 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41111018509127 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131438753839 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨54, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41111018509127 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131438753839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_55 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41094166886993 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131440754439 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨55, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41094166886993 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131440754439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_56 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82154653776943 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565721386653 / 25000000000000 : ℝ))
      (E := (cell12610 ⟨56, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82154653776943 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565721386653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_57 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82120996999389 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262889499023 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨57, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82120996999389 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262889499023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_58 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41043681706863 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565723384917 / 25000000000000 : ℝ))
      (E := (cell12610 ⟨58, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41043681706863 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565723384917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_59 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41026876496247 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565724386563 / 25000000000000 : ℝ))
      (E := (cell12610 ⟨59, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41026876496247 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565724386563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12611_40 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82696336515737 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (565673859217 / 25000000000000 : ℝ))
      (E := (cell12611 ⟨40, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82696336515737 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (565673859217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_41 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82662305124571 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262699420313 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨41, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82662305124571 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262699420313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_42 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41314148691751 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262703410721 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨42, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41314148691751 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262703410721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_43 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82594313262771 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131353703713 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨43, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82594313262771 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131353703713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_44 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82560352732769 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (282838926193 / 12500000000000 : ℝ))
      (E := (cell12611 ⟨44, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82560352732769 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (282838926193 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_45 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (20631603941009 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131357707987 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨45, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (20631603941009 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131357707987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_46 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (4124625116363 / 5000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262719425397 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨46, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (4124625116363 / 5000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262719425397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_47 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82458612393277 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262723436279 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨47, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82458612393277 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262723436279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_48 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82424745933071 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262727446869 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨48, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82424745933071 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262727446869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_49 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (10298862864721 / 12500000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131365727603 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨49, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (10298862864721 / 12500000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131365727603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_50 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82357083318643 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (226273545911 / 10000000000000 : ℝ))
      (E := (cell12611 ⟨50, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82357083318643 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (226273545911 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_51 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82323287107113 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (226273945619 / 10000000000000 : ℝ))
      (E := (cell12611 ⟨51, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82323287107113 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (226273945619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_52 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41144757127369 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131371721923 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨52, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41144757127369 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131371721923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_53 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82255764733221 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262747478307 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨53, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82255764733221 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262747478307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_54 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41111019257203 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (565687859621 / 25000000000000 : ℝ))
      (E := (cell12611 ⟨54, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41111019257203 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (565687859621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_55 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82188335570279 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (282844429907 / 12500000000000 : ℝ))
      (E := (cell12611 ⟨55, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82188335570279 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (282844429907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_56 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41077327936483 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262759477249 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨56, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41077327936483 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262759477249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_57 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (8212099939473 / 10000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131381744873 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨57, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (8212099939473 / 10000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131381744873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_58 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41043683053987 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (282845934111 / 12500000000000 : ℝ))
      (E := (cell12611 ⟨58, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41043683053987 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (282845934111 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_59 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82053755985239 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (452554296359 / 20000000000000 : ℝ))
      (E := (cell12611 ⟨59, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82053755985239 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (452554296359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12612_40 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (16539266753423 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262569384383 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨40, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (16539266753423 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262569384383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_41 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (826623026819 / 1000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262573416463 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨41, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (826623026819 / 1000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262573416463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_42 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (2065707381159 / 2500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (282822174683 / 12500000000000 : ℝ))
      (E := (cell12612 ⟨42, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (2065707381159 / 2500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (282822174683 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_43 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (5162144464421 / 6250000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (226258144427 / 10000000000000 : ℝ))
      (E := (cell12612 ⟨43, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (5162144464421 / 6250000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (226258144427 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_44 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82560351205421 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262585438399 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨44, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82560351205421 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262585438399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_45 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41263207270477 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262589437537 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨45, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41263207270477 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262589437537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_46 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (3299700056321 / 4000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262593440363 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨46, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (3299700056321 / 4000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262593440363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_47 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82458611777471 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262597445343 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨47, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82458611777471 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262597445343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_48 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (3296989824811 / 4000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131300725363 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨48, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (3296989824811 / 4000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131300725363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_49 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (16478180581513 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262605454549 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨49, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (16478180581513 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262605454549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_50 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82357083610617 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262609454631 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨50, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82357083610617 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262609454631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_51 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82323287700847 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262613448583 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨51, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82323287700847 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262613448583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_52 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41144757574909 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (11313087169 / 500000000000 : ℝ))
      (E := (cell12612 ⟨52, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41144757574909 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (11313087169 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_53 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (5140985370577 / 6250000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452524293303 / 20000000000000 : ℝ))
      (E := (cell12612 ⟨53, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (5140985370577 / 6250000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452524293303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_54 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (10277755001367 / 12500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131312742351 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨54, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (10277755001367 / 12500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131312742351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_55 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41094168683457 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (226262948513 / 10000000000000 : ℝ))
      (E := (cell12612 ⟨55, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41094168683457 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (226262948513 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_56 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41077328984647 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (70707295761 / 3125000000000 : ℝ))
      (E := (cell12612 ⟨56, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41077328984647 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (70707295761 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_57 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82121001790339 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262637477859 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨57, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82121001790339 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262637477859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_58 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41043684401227 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262641462697 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨58, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41043684401227 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262641462697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_59 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (4102687948909 / 5000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131322736993 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨59, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (4102687948909 / 5000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131322736993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12613_40 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82696331019387 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262443446123 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨40, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82696331019387 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262443446123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_41 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82662300240087 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262447468159 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨41, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82662300240087 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262447468159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_42 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82628293110039 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452490287963 / 20000000000000 : ℝ))
      (E := (cell12613 ⟨42, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82628293110039 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452490287963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_43 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (16518861919897 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131227738987 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨43, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (16518861919897 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131227738987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_44 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82560349678819 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131229732077 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨44, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82560349678819 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131229732077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_45 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (41263206659291 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565615864009 / 25000000000000 : ℝ))
      (E := (cell12613 ⟨45, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (41263206659291 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565615864009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_46 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82492500489463 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (141404215769 / 6250000000000 : ℝ))
      (E := (cell12613 ⟨46, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82492500489463 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (141404215769 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_47 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (824586111623 / 1000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (113123572571 / 5000000000000 : ℝ))
      (E := (cell12613 ⟨47, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (824586111623 / 1000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (113123572571 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_48 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82424745308077 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131237725817 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨48, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82424745308077 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131237725817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_49 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (20597725724481 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (113123972549 / 5000000000000 : ℝ))
      (E := (cell12613 ⟨49, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (20597725724481 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (113123972549 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_50 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (16471416780623 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262483447279 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨50, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (16471416780623 / 20000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262483447279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_51 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (8232328829507 / 10000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (141405468571 / 6250000000000 : ℝ))
      (E := (cell12613 ⟨51, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (8232328829507 / 10000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (141405468571 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_52 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82289516045349 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131245739989 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨52, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82289516045349 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131245739989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_53 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82255767125659 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452499102201 / 20000000000000 : ℝ))
      (E := (cell12613 ⟨53, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82255767125659 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452499102201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_54 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82222041507843 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (226249946913 / 10000000000000 : ℝ))
      (E := (cell12613 ⟨54, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82222041507843 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (226249946913 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_55 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (8218833916389 / 10000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131251734613 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨55, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (8218833916389 / 10000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131251734613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_56 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (41077330032963 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262507507923 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨56, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (41077330032963 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262507507923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_57 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82121004186217 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131255761249 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨57, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82121004186217 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131255761249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_58 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (41043685748583 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262515509093 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨58, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (41043685748583 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262515509093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_59 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (20513440492829 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131259761413 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨59, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (20513440492829 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131259761413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12614_40 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20674082068139 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (70697422019 / 3125000000000 : ℝ))
      (E := (cell12614 ⟨40, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20674082068139 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (70697422019 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_41 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20665574449783 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (14139509479 / 625000000000 : ℝ))
      (E := (cell12614 ⟨41, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20665574449783 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (14139509479 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_42 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82628290974539 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (90493021511 / 4000000000000 : ℝ))
      (E := (cell12614 ⟨42, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82628290974539 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (90493021511 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_43 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (41297153884509 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262329508539 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨43, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (41297153884509 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262329508539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_44 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20640087038241 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262333545639 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨44, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20640087038241 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262333545639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_45 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82526412096919 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (226233753033 / 10000000000000 : ℝ))
      (E := (cell12614 ⟨45, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82526412096919 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (226233753033 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_46 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82492499571573 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (22623415201 / 1000000000000 : ℝ))
      (E := (cell12614 ⟨46, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82492499571573 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (22623415201 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_47 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20614652636941 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131172756707 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨47, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20614652636941 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131172756707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_48 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82424744996477 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262349567447 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨48, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82424744996477 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262349567447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_49 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20597725722211 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262353562401 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨49, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20597725722211 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262353562401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_50 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (41178542098069 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262357555001 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨50, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (41178542098069 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262357555001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_51 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (4116164444489 / 5000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131180771427 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨51, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (4116164444489 / 5000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131180771427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_52 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20572379235333 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262365582377 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨52, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20572379235333 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262365582377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_53 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82255768322499 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (70699048523 / 3125000000000 : ℝ))
      (E := (cell12614 ⟨53, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82255768322499 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (70699048523 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_54 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82222043005129 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262373568969 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨54, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82222043005129 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262373568969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_55 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (10273542620151 / 12500000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (113118878441 / 5000000000000 : ℝ))
      (E := (cell12614 ⟨55, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (10273542620151 / 12500000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (113118878441 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_56 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (5134666385179 / 6250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262381548843 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨56, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (5134666385179 / 6250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262381548843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_57 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82121006582363 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131192782263 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨57, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82121006582363 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131192782263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_58 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (8208737419211 / 10000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131194806039 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨58, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (8208737419211 / 10000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131194806039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_59 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82053764964647 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (226239356913 / 10000000000000 : ℝ))
      (E := (cell12614 ⟨59, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82053764964647 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (226239356913 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12615_40 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (82696325526619 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262191618581 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨40, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (82696325526619 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262191618581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_41 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16532459071807 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262195620669 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨41, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16532459071807 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262195620669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_42 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (82628288839859 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (28277495407 / 1250000000000 : ℝ))
      (E := (cell12615 ⟨42, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (82628288839859 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (28277495407 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_43 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16518861187867 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (452440730717 / 20000000000000 : ℝ))
      (E := (cell12615 ⟨43, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16518861187867 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (452440730717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_44 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (5160021664241 / 6250000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (90488304961 / 4000000000000 : ℝ))
      (E := (cell12615 ⟨44, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (5160021664241 / 6250000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (90488304961 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_45 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16505282175193 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131105830209 / 50000000000000 : ℝ))
      (E := (cell12615 ⟨45, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16505282175193 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131105830209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_46 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16498499730871 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262215643753 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨46, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16498499730871 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262215643753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_47 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (82458609933863 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131109815663 / 50000000000000 : ℝ))
      (E := (cell12615 ⟨47, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (82458609933863 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131109815663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_48 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (20606186171369 / 25000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (282777960039 / 12500000000000 : ℝ))
      (E := (cell12615 ⟨48, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (20606186171369 / 25000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (282777960039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_49 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (3295636115213 / 4000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (17673653679 / 781250000000 : ℝ))
      (E := (cell12615 ⟨49, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (3295636115213 / 4000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (17673653679 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_50 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16471416897937 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262231659851 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨50, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16471416897937 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262231659851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_51 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (82323289484977 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (35347431949 / 1562500000000 : ℝ))
      (E := (cell12615 ⟨51, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (82323289484977 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (35347431949 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_52 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16457903567553 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262239681981 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨52, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16457903567553 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262239681981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_53 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41127884759877 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262243650751 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨53, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41127884759877 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262243650751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_54 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (10277755562849 / 12500000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262247666087 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨54, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (10277755562849 / 12500000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262247666087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_55 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41094171379433 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (226225166573 / 10000000000000 : ℝ))
      (E := (cell12615 ⟨55, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41094171379433 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (226225166573 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_56 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16430932852021 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262255705349 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨56, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16430932852021 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262255705349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_57 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (82121008978777 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262259722223 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨57, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (82121008978777 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262259722223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_58 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16417475377457 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262263712491 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨58, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16417475377457 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262263712491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_59 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41026883979087 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (226226773127 / 10000000000000 : ℝ))
      (E := (cell12615 ⟨59, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41026883979087 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (226226773127 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12616_40 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41348161390789 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262065788041 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨40, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41348161390789 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262065788041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_41 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (20665573229949 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262069780247 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨41, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (20665573229949 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262069780247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_42 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41314143353 / 50000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452414756591 / 20000000000000 : ℝ))
      (E := (cell12616 ⟨42, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41314143353 / 50000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452414756591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_43 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41297152055217 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452415559099 / 20000000000000 : ℝ))
      (E := (cell12616 ⟨43, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41297152055217 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452415559099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_44 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82560345103493 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262081816979 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨44, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82560345103493 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262081816979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_45 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (2063160241393 / 2500000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131042893723 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨45, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (2063160241393 / 2500000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131042893723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_46 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82492497737809 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262089823263 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨46, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82492497737809 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262089823263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_47 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82458609320597 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262093805157 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨47, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82458609320597 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262093805157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_48 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82424744375073 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262097790229 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨48, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82424744375073 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262097790229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_49 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82390902872367 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452420367093 / 20000000000000 : ℝ))
      (E := (cell12616 ⟨49, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82390902872367 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (452420367093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_50 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (20589271195939 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565526455201 / 25000000000000 : ℝ))
      (E := (cell12616 ⟨50, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (20589271195939 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565526455201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_51 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82323290080663 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262109802779 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨51, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82323290080663 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262109802779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_52 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82289518734649 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (141382114863 / 6250000000000 : ℝ))
      (E := (cell12616 ⟨52, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82289518734649 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (141382114863 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_53 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82255770717423 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565529451263 / 25000000000000 : ℝ))
      (E := (cell12616 ⟨53, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82255770717423 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (565529451263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_54 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82222046000833 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262121819551 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨54, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82222046000833 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262121819551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_55 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41094172278433 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131062909523 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨55, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41094172278433 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131062909523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_56 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (20538666589413 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262129859207 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨56, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (20538666589413 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262129859207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_57 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (41060505687729 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262133818171 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨57, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (41060505687729 / 50000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262133818171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_58 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (20521844895673 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131068934747 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨58, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (20521844895673 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131068934747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_59 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82053770951897 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262141831689 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨59, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82053770951897 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262141831689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12617_40 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (82696320037431 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (565484988563 / 25000000000000 : ℝ))
      (E := (cell12617 ⟨40, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (82696320037431 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (565484988563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_41 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41331145240707 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130971997689 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨41, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41331145240707 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130971997689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_42 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (82628284572961 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261947988963 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨42, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (82628284572961 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261947988963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_43 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (20648575570579 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261951993079 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨43, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (20648575570579 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261951993079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_44 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (20640085894969 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (452391201367 / 20000000000000 : ℝ))
      (E := (cell12617 ⟨44, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (20640085894969 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (452391201367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_45 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (10315801054523 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261959970271 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨45, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (10315801054523 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261959970271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_46 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41246248410967 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (282745499969 / 12500000000000 : ℝ))
      (E := (cell12617 ⟨46, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41246248410967 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (282745499969 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_47 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41229304353983 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (565491994001 / 25000000000000 : ℝ))
      (E := (cell12617 ⟨47, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41229304353983 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (565491994001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_48 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (82424744065267 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (141373250941 / 6250000000000 : ℝ))
      (E := (cell12617 ⟨48, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (82424744065267 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (141373250941 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_49 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (8239090286497 / 10000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261975997109 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨49, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (8239090286497 / 10000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261975997109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_50 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (5147317817397 / 6250000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261980037861 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨50, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (5147317817397 / 6250000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261980037861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_51 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (16464658135367 / 20000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (226198401699 / 10000000000000 : ℝ))
      (E := (cell12617 ⟨51, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (16464658135367 / 20000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (226198401699 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_52 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (5143094976999 / 6250000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261987990841 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨52, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (5143094976999 / 6250000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261987990841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_53 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41127885957753 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130996007821 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨53, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41127885957753 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130996007821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_54 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (328888189997 / 400000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (452399205873 / 20000000000000 : ℝ))
      (E := (cell12617 ⟨54, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (328888189997 / 400000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (452399205873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_55 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41094173177603 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2262000028773 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨55, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41094173177603 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2262000028773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_56 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41077334227751 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (113100200521 / 5000000000000 : ℝ))
      (E := (cell12617 ⟨56, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41077334227751 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (113100200521 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_57 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (10265126721551 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (226200802979 / 10000000000000 : ℝ))
      (E := (cell12617 ⟨57, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (10265126721551 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (226200802979 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_58 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (82087382278331 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1131006011963 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨58, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (82087382278331 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1131006011963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_59 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41026886972907 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (565504011987 / 25000000000000 : ℝ))
      (E := (cell12617 ⟨59, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41026886972907 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (565504011987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12618_40 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41348158647089 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565453558673 / 25000000000000 : ℝ))
      (E := (cell12618 ⟨40, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41348158647089 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565453558673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_41 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82662288043889 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261818207297 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨41, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82662288043889 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261818207297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_42 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41314141220371 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130911095899 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨42, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41314141220371 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130911095899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_43 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82594300454981 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130913123169 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨43, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82594300454981 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130913123169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_44 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (16512068411401 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130915096797 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨44, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (16512068411401 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130915096797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_45 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82526407217357 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261834208893 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨45, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82526407217357 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261834208893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_46 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82492495906731 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (22618382321 / 1000000000000 : ℝ))
      (E := (cell12618 ⟨46, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82492495906731 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (22618382321 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_47 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82458608095969 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261842202771 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨47, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82458608095969 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261842202771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_48 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82424743756059 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261846236937 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨48, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82424743756059 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261846236937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_49 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82390902858133 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130925107399 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨49, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82390902858133 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130925107399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_50 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82357085373471 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (141365890753 / 6250000000000 : ℝ))
      (E := (cell12618 ⟨50, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82357085373471 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (141365890753 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_51 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (16464658254699 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261858228367 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨51, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (16464658254699 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261858228367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_52 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82289520529769 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130931129561 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨52, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82289520529769 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130931129561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_53 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82255773114003 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130933141259 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨53, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82255773114003 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130933141259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_54 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (16444409799609 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261870236459 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨54, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (16444409799609 / 20000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261870236459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_55 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82188348153887 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261874235817 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨55, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82188348153887 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261874235817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_56 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82154670553657 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261878277219 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨56, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82154670553657 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261878277219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_57 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41060508084813 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261882297939 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨57, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41060508084813 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261882297939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_58 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (410436924871 / 500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130943147057 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨58, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (410436924871 / 500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130943147057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_59 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41026888469963 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261890261673 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨59, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41026888469963 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261890261673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12619_40 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (4134815727591 / 5000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (282711056643 / 12500000000000 : ℝ))
      (E := (cell12619 ⟨40, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (4134815727591 / 5000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (282711056643 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_41 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82662285607221 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261692474769 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨41, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82662285607221 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261692474769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_42 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (41314140154671 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452339301807 / 20000000000000 : ℝ))
      (E := (cell12619 ⟨42, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (41314140154671 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452339301807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_43 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82594298628429 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261700496463 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨43, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82594298628429 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261700496463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_44 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (41280170267439 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130852247463 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨44, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (41280170267439 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130852247463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_45 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82526405999237 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565427125829 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨45, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82526405999237 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565427125829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_46 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82492494992199 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261712520309 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨46, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82492494992199 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261712520309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_47 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82458607484607 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261716485461 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨47, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82458607484607 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261716485461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_48 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (10303092930931 / 12500000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130860257401 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨48, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (10303092930931 / 12500000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130860257401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_49 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (41195451425929 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (226172448853 / 10000000000000 : ℝ))
      (E := (cell12619 ⟨49, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (41195451425929 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (226172448853 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_50 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (41178542834557 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261728522341 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨50, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (41178542834557 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261728522341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_51 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82323291870641 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261732495913 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨51, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82323291870641 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261732495913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_52 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (20572380357001 / 25000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (226173652461 / 10000000000000 : ℝ))
      (E := (cell12619 ⟨52, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (20572380357001 / 25000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (226173652461 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_53 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82255774312913 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (28271756833 / 1250000000000 : ℝ))
      (E := (cell12619 ⟨53, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82255774312913 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (28271756833 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_54 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82222050497217 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565436139743 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨54, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82222050497217 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565436139743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_55 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (20547087488227 / 25000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130874279183 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨55, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (20547087488227 / 25000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130874279183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_56 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (16430934530423 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (35339883459 / 1562500000000 : ℝ))
      (E := (cell12619 ⟨56, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (16430934530423 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (35339883459 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_57 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (8212101856711 / 10000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565439140871 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨57, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (8212101856711 / 10000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565439140871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_58 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82087387670301 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261760561733 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨58, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82087387670301 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261760561733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_59 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82053779934233 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261764532053 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨59, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82053779934233 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261764532053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12620_40 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (16539262362071 / 20000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565390696457 / 25000000000000 : ℝ))
      (E := (cell12620 ⟨40, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (16539262362071 / 20000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565390696457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_41 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (8266228317141 / 10000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130783398897 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨41, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (8266228317141 / 10000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130783398897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_42 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41314139089381 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (22615708231 / 1000000000000 : ℝ))
      (E := (cell12620 ⟨42, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41314139089381 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (22615708231 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_43 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41297148401329 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452314960453 / 20000000000000 : ℝ))
      (E := (cell12620 ⟨43, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41297148401329 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452314960453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_44 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82560339013497 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261578793161 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨44, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82560339013497 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261578793161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_45 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41263202390913 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (56539569867 / 2500000000000 : ℝ))
      (E := (cell12620 ⟨45, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41263202390913 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (56539569867 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_46 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41246247039169 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261586805499 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨46, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41246247039169 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261586805499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_47 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41229303436939 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130795412037 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨47, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41229303436939 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130795412037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_48 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41212371569717 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261594789723 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨48, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41212371569717 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261594789723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_49 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41195451423071 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565399704577 / 25000000000000 : ℝ))
      (E := (cell12620 ⟨49, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41195451423071 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565399704577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_50 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82357085965281 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (113080142437 / 5000000000000 : ℝ))
      (E := (cell12620 ⟨50, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82357085965281 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (113080142437 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_51 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41161646234137 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (18092854557 / 800000000000 : ℝ))
      (E := (cell12620 ⟨51, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41161646234137 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (18092854557 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_52 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (8228952232669 / 10000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130805423163 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨52, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (8228952232669 / 10000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130805423163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_53 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82255775512237 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452322961601 / 20000000000000 : ℝ))
      (E := (cell12620 ⟨53, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82255775512237 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452322961601 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_54 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41111025998383 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261618819697 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨54, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41111025998383 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261618819697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_55 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82188351752269 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261622819141 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨55, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82188351752269 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261622819141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_56 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41077337375439 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565406715501 / 25000000000000 : ℝ))
      (E := (cell12620 ⟨56, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41077337375439 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565406715501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_57 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82121020964863 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261630826421 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨57, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82121020964863 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261630826421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_58 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82087390366633 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452326977189 / 20000000000000 : ℝ))
      (E := (cell12620 ⟨58, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82087390366633 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452326977189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_59 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (16410756585747 / 20000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261638859087 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨59, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (16410756585747 / 20000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261638859087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12621_40 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (16539261813957 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (17667477463 / 781250000000 : ℝ))
      (E := (cell12621 ⟨40, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (16539261813957 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (17667477463 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_41 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (16532456147291 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (226144111761 / 10000000000000 : ℝ))
      (E := (cell12621 ⟨41, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (16532456147291 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (226144111761 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_42 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82628276049001 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130722566997 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨42, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82628276049001 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130722566997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_43 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (8259429497767 / 10000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (452289832749 / 20000000000000 : ℝ))
      (E := (cell12621 ⟨43, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (8259429497767 / 10000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (452289832749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_44 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82560337492861 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2208450339 / 97656250000 : ℝ))
      (E := (cell12621 ⟨44, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82560337492861 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2208450339 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_45 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41263201782561 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130728570923 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨45, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41263201782561 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130728570923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_46 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (20623123291287 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (45229222931 / 2000000000000 : ℝ))
      (E := (cell12621 ⟨46, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (20623123291287 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (45229222931 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_47 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82458606263783 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130732579853 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨47, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82458606263783 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130732579853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_48 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41212371416009 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565367294889 / 25000000000000 : ℝ))
      (E := (cell12621 ⟨48, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41212371416009 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565367294889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_49 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41195451420493 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261473145181 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨49, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41195451420493 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261473145181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_50 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (8235708626197 / 10000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (141342323267 / 6250000000000 : ℝ))
      (E := (cell12621 ⟨50, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (8235708626197 / 10000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (141342323267 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_51 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41161646533197 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130740599753 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨51, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41161646533197 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130740599753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_52 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (3291580929033 / 4000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261485165251 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨52, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (3291580929033 / 4000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261485165251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_53 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82255776711973 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261489184707 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨53, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82255776711973 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261489184707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_54 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82222053496691 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565373298961 / 25000000000000 : ℝ))
      (E := (cell12621 ⟨54, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82222053496691 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565373298961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_55 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82188353551971 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261497195421 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨55, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82188353551971 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261497195421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_56 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (10269334606243 / 12500000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (226150117999 / 10000000000000 : ℝ))
      (E := (cell12621 ⟨56, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (10269334606243 / 12500000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (226150117999 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_57 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41060511681441 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261505205033 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨57, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41060511681441 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261505205033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_58 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (16417478612639 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261509207591 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨58, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (16417478612639 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261509207591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_59 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82053785923431 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130756621389 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨59, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82053785923431 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130756621389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12622_40 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82696306330107 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261311558937 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨40, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82696306330107 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261311558937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_41 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20665569575589 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565328887937 / 25000000000000 : ℝ))
      (E := (cell12622 ⟨41, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20665569575589 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565328887937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_42 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41314136960029 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452263911859 / 20000000000000 : ℝ))
      (E := (cell12622 ⟨42, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41314136960029 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452263911859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_43 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82594293153463 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452264704419 / 20000000000000 : ℝ))
      (E := (cell12622 ⟨43, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82594293153463 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452264704419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_44 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82560335972969 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261327556853 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨44, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82560335972969 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261327556853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_45 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41263201174563 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452266308963 / 20000000000000 : ℝ))
      (E := (cell12622 ⟨45, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41263201174563 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452266308963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_46 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20623123063157 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261335543467 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨46, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20623123063157 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261335543467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_47 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41229302827161 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (70666860977 / 3125000000000 : ℝ))
      (E := (cell12622 ⟨47, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41229302827161 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (70666860977 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_48 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82424742525197 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (45226871329 / 2000000000000 : ℝ))
      (E := (cell12622 ⟨48, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82424742525197 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (45226871329 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_49 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82390902836391 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261347587053 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨49, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82390902836391 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261347587053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_50 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82357086559183 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130675775957 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨50, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82357086559183 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130675775957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_51 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (16464658733 / 20000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261355576559 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨51, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (16464658733 / 20000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261355576559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_52 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (8228952412541 / 10000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261359599429 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨52, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (8228952412541 / 10000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261359599429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_53 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82255777912123 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (8833451401 / 390625000000 : ℝ))
      (E := (cell12622 ⟨53, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82255777912123 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (8833451401 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_54 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82222054996993 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (90454702771 / 4000000000000 : ℝ))
      (E := (cell12622 ⟨54, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82222054996993 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (90454702771 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_55 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20547088838003 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (17666965383 / 781250000000 : ℝ))
      (E := (cell12622 ⟨55, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20547088838003 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (17666965383 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_56 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82154678949313 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261375613569 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨56, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82154678949313 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261375613569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_57 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82121025761169 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261379581041 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨57, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82121025761169 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261379581041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_58 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82087395759989 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (282672948229 / 12500000000000 : ℝ))
      (E := (cell12622 ⟨58, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82087395759989 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (282672948229 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_59 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41026894459161 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (113069381197 / 5000000000000 : ℝ))
      (E := (cell12622 ⟨59, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41026894459161 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (113069381197 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12623_40 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82696303591323 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261185940623 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨40, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82696303591323 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261185940623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_41 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82662275869113 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261189982677 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨41, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82662275869113 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261189982677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_42 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (16525654358387 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (90447759257 / 4000000000000 : ℝ))
      (E := (cell12623 ⟨42, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (16525654358387 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (90447759257 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_43 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41297145665019 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261197994933 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨43, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41297145665019 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261197994933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_44 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41280167226911 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565300490869 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨44, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41280167226911 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565300490869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_45 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82526401133837 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130603001793 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨45, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82526401133837 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130603001793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_46 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82492491340779 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130604998123 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨46, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82492491340779 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130604998123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_47 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41229302522747 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261213998747 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨47, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41229302522747 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261213998747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_48 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41212371109487 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261218009329 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨48, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41212371109487 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261218009329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_49 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41195451416177 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261221967071 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨49, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41195451416177 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261221967071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_50 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82357086856919 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261225987663 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨50, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82357086856919 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261225987663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_51 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (20580823566023 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130615004891 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨51, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (20580823566023 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130615004891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_52 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (20572381256361 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130616985897 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨52, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (20572381256361 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130616985897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_53 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41127889556343 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (70663687153 / 3125000000000 : ℝ))
      (E := (cell12623 ⟨53, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41127889556343 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (70663687153 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_54 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82222056497671 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261241999059 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨54, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82222056497671 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261241999059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_55 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82188357152393 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (7066393747 / 312500000000 : ℝ))
      (E := (cell12623 ⟨55, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82188357152393 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (7066393747 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_56 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41077340524493 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (452250008901 / 20000000000000 : ℝ))
      (E := (cell12623 ⟨56, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41077340524493 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (452250008901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_57 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41060514079861 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (452250802717 / 20000000000000 : ℝ))
      (E := (cell12623 ⟨57, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41060514079861 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (452250802717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_58 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82087398457013 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (226125802067 / 10000000000000 : ℝ))
      (E := (cell12623 ⟨58, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82087398457013 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (226125802067 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_59 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82053791913407 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130631030879 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨59, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82053791913407 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130631030879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12624_40 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82696300853431 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261060436547 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨40, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82696300853431 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261060436547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_41 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (3306490937469 / 4000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130532205201 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨41, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (3306490937469 / 4000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130532205201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_42 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82628269664629 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261068459177 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨42, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82628269664629 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261068459177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_43 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41297144753697 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565268116161 / 25000000000000 : ℝ))
      (E := (cell12624 ⟨43, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41297144753697 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565268116161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_44 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82560332935419 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261076425843 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨44, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82560332935419 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261076425843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_45 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (16505279983851 / 20000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (452216091861 / 20000000000000 : ℝ))
      (E := (cell12624 ⟨45, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (16505279983851 / 20000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (452216091861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_46 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (103115613037 / 125000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261084446011 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨46, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (103115613037 / 125000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261084446011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_47 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (824586044373 / 1000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565272110813 / 25000000000000 : ℝ))
      (E := (cell12624 ⟨47, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (824586044373 / 1000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565272110813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_48 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41212370956673 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (226109244927 / 10000000000000 : ℝ))
      (E := (cell12624 ⟨48, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41212370956673 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (226109244927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_49 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41195451414439 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261096462089 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨49, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41195451414439 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261096462089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_50 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82357087155177 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (90444019181 / 4000000000000 : ℝ))
      (E := (cell12624 ⟨50, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82357087155177 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (90444019181 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_51 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (8232329486367 / 10000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (113055222009 / 5000000000000 : ℝ))
      (E := (cell12624 ⟨51, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (8232329486367 / 10000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (113055222009 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_52 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82289525925927 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (452221691883 / 20000000000000 : ℝ))
      (E := (cell12624 ⟨52, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82289525925927 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (452221691883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_53 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82255780313661 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (282639059429 / 12500000000000 : ℝ))
      (E := (cell12624 ⟨53, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82255780313661 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (282639059429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_54 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (3288882319949 / 4000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261116485199 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨54, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (3288882319949 / 4000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261116485199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_55 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41094179476557 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261120485473 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨55, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41094179476557 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261120485473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_56 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41077341574481 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130562236401 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨56, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41077341574481 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130562236401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_57 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82121030558543 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261128502667 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨57, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82121030558543 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261128502667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_58 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82087401154267 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565283128027 / 25000000000000 : ℝ))
      (E := (cell12624 ⟨58, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82087401154267 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (565283128027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_59 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41026897454343 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (45222729941 / 2000000000000 : ℝ))
      (E := (cell12624 ⟨59, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41026897454343 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (45222729941 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

end BstLean.Part268
