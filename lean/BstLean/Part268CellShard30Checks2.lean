import BstLean.Part268CellShard30Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13100_40 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (5168348955857 / 6250000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204851358269 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨40, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (5168348955857 / 6250000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204851358269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_41 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (16531932099063 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (440971069259 / 20000000000000 : ℝ))
      (E := (cell13100 ⟨41, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (16531932099063 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (440971069259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_42 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41312880598867 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204859360583 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨42, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41312880598867 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204859360583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_43 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41295942685741 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (88194535997 / 4000000000000 : ℝ))
      (E := (cell13100 ⟨43, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41295942685741 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (88194535997 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_44 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (82558032987219 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (110243370201 / 5000000000000 : ℝ))
      (E := (cell13100 ⟨44, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (82558032987219 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (110243370201 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_45 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41262102007877 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102435715029 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨45, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41262102007877 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102435715029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_46 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (82490398428043 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204875417257 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨46, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (82490398428043 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204875417257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_47 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (16491323239037 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102439740689 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨47, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (16491323239037 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102439740689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_48 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (82422857288427 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (110244175113 / 5000000000000 : ℝ))
      (E := (cell13100 ⟨48, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (82422857288427 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (110244175113 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_49 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (41194560839579 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204887477339 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨49, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (41194560839579 / 50000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204887477339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_50 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (2573606541841 / 3125000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102445760937 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨50, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (2573606541841 / 3125000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102445760937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_51 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (82321720239363 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204895514931 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨51, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (82321720239363 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204895514931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_52 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (10286006794041 / 12500000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (275612439047 / 12500000000000 : ℝ))
      (E := (cell13100 ⟨52, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (10286006794041 / 12500000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (275612439047 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_53 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (20563602912441 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (55122589249 / 2500000000000 : ℝ))
      (E := (cell13100 ⟨53, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (20563602912441 / 25000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (55122589249 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_54 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (10277599012971 / 12500000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204907565979 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨54, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (10277599012971 / 12500000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204907565979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_55 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (82187195686577 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (13780697593 / 625000000000 : ℝ))
      (E := (cell13100 ⟨55, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (82187195686577 / 100000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (13780697593 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_56 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (16430724474113 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204915594449 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨56, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (16430724474113 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204915594449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_57 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (16424014425649 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (551229904703 / 25000000000000 : ℝ))
      (E := (cell13100 ⟨57, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (16424014425649 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (551229904703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_58 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (16417308986453 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204923624457 / 100000000000000 : ℝ))
      (E := (cell13100 ⟨58, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (16417308986453 / 20000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (2204923624457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13100_59 : CellCertificate 13100 (875843412266401 / 10000000000000000 : ℝ) (320675081395459 / 200000000000000000 : ℝ) (323640126141257 / 10000000000000000 : ℝ)
    (cell13100 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · norm_num [cell13100]
  · have h := gap_lower (n := 13100) (a := (8205304075541 / 10000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102463833017 / 50000000000000 : ℝ))
      (E := (cell13100 ⟨59, by decide⟩).energy) (xi := (323640126141257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13100 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13100) (a := (8205304075541 / 10000000000000 : ℝ)) (b := (78589683071 / 50000000000000 : ℝ)) (q := (1102463833017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13100]

theorem cert13101_40 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82693569324671 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440947863521 / 20000000000000 : ℝ))
      (E := (cell13101 ⟨40, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82693569324671 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440947863521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_41 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82659646532373 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102371681019 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨41, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82659646532373 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102371681019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_42 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (16525149448177 / 20000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102373686997 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨42, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (16525149448177 / 20000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102373686997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_43 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (1032398392759 / 1250000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551187838049 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨43, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (1032398392759 / 1250000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551187838049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_44 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (4127900952127 / 5000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102377706453 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨44, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (4127900952127 / 5000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102377706453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_45 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82524190077153 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204759436751 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨45, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82524190077153 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204759436751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_46 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41245192247757 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551190855451 / 25000000000000 : ℝ))
      (E := (cell13101 ⟨46, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41245192247757 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (551190855451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_47 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (20614150567181 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102383712437 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨47, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (20614150567181 / 25000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102383712437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_48 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82422843368029 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204771443679 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨48, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82422843368029 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204771443679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_49 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82389107764819 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (55119386893 / 2500000000000 : ℝ))
      (E := (cell13101 ⟨49, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82389107764819 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (55119386893 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_50 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41177697715313 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204779459273 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨50, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41177697715313 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204779459273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_51 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (658573650697 / 800000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204783509433 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨51, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (658573650697 / 800000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204783509433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_52 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82288040456133 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204787505007 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨52, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82288040456133 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204787505007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_53 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (10281799719951 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204791560767 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨53, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (10281799719951 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204791560767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_54 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82220778219647 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102397777503 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨54, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82220778219647 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102397777503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_55 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (16437436361697 / 20000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204799543037 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨55, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (16437436361697 / 20000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204799543037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_56 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (41076804249249 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440960716011 / 20000000000000 : ℝ))
      (E := (cell13101 ⟨56, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (41076804249249 / 50000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (440960716011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_57 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82120058262197 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204807602777 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨57, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82120058262197 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204807602777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_58 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (10260816384029 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204811606827 / 100000000000000 : ℝ))
      (E := (cell13101 ⟨58, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (10260816384029 / 12500000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (2204811606827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13101_59 : CellCertificate 13101 (13684642033051 / 156250000000000 : ℝ) (320650596448507 / 200000000000000000 : ℝ) (323614855171903 / 10000000000000000 : ℝ)
    (cell13101 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · norm_num [cell13101]
  · have h := gap_lower (n := 13101) (a := (82053026901387 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102407823427 / 50000000000000 : ℝ))
      (E := (cell13101 ⟨59, by decide⟩).energy) (xi := (323614855171903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13101 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13101) (a := (82053026901387 / 100000000000000 : ℝ)) (b := (78583615413 / 50000000000000 : ℝ)) (q := (1102407823427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13101]

theorem cert13102_40 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41346777678883 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102313665743 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨40, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41346777678883 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102313665743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_41 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (20664908142891 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102315686771 / 50000000000000 : ℝ))
      (E := (cell13102 ⟨41, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (20664908142891 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (1102315686771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_42 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (10328216660771 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (17223713931 / 781250000000 : ℝ))
      (E := (cell13102 ⟨42, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (10328216660771 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (17223713931 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_43 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (8259185747209 / 10000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440927871817 / 20000000000000 : ℝ))
      (E := (cell13102 ⟨43, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (8259185747209 / 10000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440927871817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_44 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (10319750637499 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204643417557 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨44, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (10319750637499 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204643417557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_45 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (82524176140681 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (220464743921 / 10000000000000 : ℝ))
      (E := (cell13102 ⟨45, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (82524176140681 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (220464743921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_46 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (16498074113023 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440930284423 / 20000000000000 : ℝ))
      (E := (cell13102 ⟨46, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (16498074113023 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440930284423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_47 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (10307073543049 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440931084617 / 20000000000000 : ℝ))
      (E := (cell13102 ⟨47, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (10307073543049 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440931084617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_48 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (82422829449759 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551164859959 / 25000000000000 : ℝ))
      (E := (cell13102 ⟨48, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (82422829449759 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (551164859959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_49 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41194546926303 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (220466346987 / 10000000000000 : ℝ))
      (E := (cell13102 ⟨49, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41194546926303 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (220466346987 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_50 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (16471076304893 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (27558343881 / 1250000000000 : ℝ))
      (E := (cell13102 ⟨50, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (16471076304893 / 20000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (27558343881 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_51 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (20580423109253 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (275583937463 / 12500000000000 : ℝ))
      (E := (cell13102 ⟨51, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (20580423109253 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (275583937463 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_52 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (82288026562063 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (88187022099 / 4000000000000 : ℝ))
      (E := (cell13102 ⟨52, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (82288026562063 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (88187022099 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_53 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (10281797983947 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204679547343 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨53, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (10281797983947 / 12500000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204679547343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_54 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (82220764337647 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440936707961 / 20000000000000 : ℝ))
      (E := (cell13102 ⟨54, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (82220764337647 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440936707961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_55 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (41093583966257 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (55117189631 / 2500000000000 : ℝ))
      (E := (cell13102 ⟨55, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (41093583966257 / 50000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (55117189631 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_56 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (1643071892571 / 2000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440938312287 / 20000000000000 : ℝ))
      (E := (cell13102 ⟨56, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (1643071892571 / 2000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (440938312287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_57 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (20530011099567 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204695582517 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨57, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (20530011099567 / 25000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204695582517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_58 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (82086517214317 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204699644179 / 100000000000000 : ℝ))
      (E := (cell13102 ⟨58, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (82086517214317 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (2204699644179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13102_59 : CellCertificate 13102 (875790771810311 / 10000000000000000 : ℝ) (400782644050419 / 250000000000000000 : ℝ) (16179479408871 / 500000000000000 : ℝ)
    (cell13102 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · norm_num [cell13102]
  · have h := gap_lower (n := 13102) (a := (82053013049481 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (44094072469 / 2000000000000 : ℝ))
      (E := (cell13102 ⟨59, by decide⟩).energy) (xi := (16179479408871 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13102 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13102) (a := (82053013049481 / 100000000000000 : ℝ)) (b := (157155097391 / 100000000000000 : ℝ)) (q := (44094072469 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13102]

theorem cert13103_40 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20673385348249 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204515341127 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨40, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20673385348249 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204515341127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_41 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (8265961861289 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204519380807 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨41, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (8265961861289 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204519380807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_42 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (5164107458349 / 6250000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (275565423513 / 12500000000000 : ℝ))
      (E := (cell13103 ⟨42, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (5164107458349 / 6250000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (275565423513 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_43 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (10323980440699 / 12500000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204527420593 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨43, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (10323980440699 / 12500000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204527420593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_44 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41278995579787 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551132854493 / 25000000000000 : ℝ))
      (E := (cell13103 ⟨44, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41278995579787 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (551132854493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_45 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (4126208110317 / 5000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204535437433 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨45, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (4126208110317 / 5000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204535437433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_46 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20622589159211 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (3444592933 / 156250000000 : ℝ))
      (E := (cell13103 ⟨46, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20622589159211 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (3444592933 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_47 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20614143605547 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204543476013 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨47, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20614143605547 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204543476013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_48 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (5151425970851 / 6250000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102273745367 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨48, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (5151425970851 / 6250000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102273745367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_49 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (82389079942519 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440910303757 / 20000000000000 : ℝ))
      (E := (cell13103 ⟨49, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (82389079942519 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440910303757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_50 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (8235536762043 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204555498437 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨50, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (8235536762043 / 10000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204555498437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_51 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (82321678539023 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204559544789 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨51, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (82321678539023 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204559544789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_52 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20572003167529 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204563536647 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨52, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20572003167529 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204563536647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_53 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41127184992833 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204567588783 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨53, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41127184992833 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204567588783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_54 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (82220750457769 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204571579491 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨54, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (82220750457769 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204571579491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_55 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (82187154058663 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102287811609 / 50000000000000 : ℝ))
      (E := (cell13103 ⟨55, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (82187154058663 / 100000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (1102287811609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_56 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41076790380361 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204579597751 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨56, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41076790380361 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204579597751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_57 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (41060015268229 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (34446619019 / 1562500000000 : ℝ))
      (E := (cell13103 ⟨57, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (41060015268229 / 50000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (34446619019 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_58 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (2052162583963 / 2500000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204587677309 / 100000000000000 : ℝ))
      (E := (cell13103 ⟨58, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (2052162583963 / 2500000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (2204587677309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13103_59 : CellCertificate 13103 (437882228675329 / 5000000000000000 : ℝ) (400752047212609 / 250000000000000000 : ℝ) (323564325156819 / 10000000000000000 : ℝ)
    (cell13103 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · norm_num [cell13103]
  · have h := gap_lower (n := 13103) (a := (20513249799923 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440918331011 / 20000000000000 : ℝ))
      (E := (cell13103 ⟨59, by decide⟩).energy) (xi := (323564325156819 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13103 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13103) (a := (20513249799923 / 25000000000000 : ℝ)) (b := (39285741459 / 25000000000000 : ℝ)) (q := (440918331011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13103]

theorem cert13104_40 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82693527430359 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204403405317 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨40, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82693527430359 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204403405317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_41 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (20664901164087 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (440881488529 / 20000000000000 : ℝ))
      (E := (cell13104 ⟨41, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (20664901164087 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (440881488529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_42 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (20656426345783 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551102861909 / 25000000000000 : ℝ))
      (E := (cell13104 ⟨42, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (20656426345783 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551102861909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_43 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (3303673183249 / 4000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102207738933 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨43, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (3303673183249 / 4000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102207738933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_44 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (10319747152661 / 12500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204419473031 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨44, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (10319747152661 / 12500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204419473031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_45 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (5157759267133 / 6250000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (88176939613 / 4000000000000 : ℝ))
      (E := (cell13104 ⟨45, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (5157759267133 / 6250000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (88176939613 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_46 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82490342710703 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551106867241 / 25000000000000 : ℝ))
      (E := (cell13104 ⟨46, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82490342710703 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551106867241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_47 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82456560502111 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (220443152471 / 10000000000000 : ℝ))
      (E := (cell13104 ⟨47, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82456560502111 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (220443152471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_48 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (206057004049 / 250000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204435537401 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨48, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (206057004049 / 250000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204435537401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_49 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41194533017279 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204439563469 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨49, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41194533017279 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204439563469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_50 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (2058883842963 / 2500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (34444430331 / 1562500000000 : ℝ))
      (E := (cell13104 ⟨50, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (2058883842963 / 2500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (34444430331 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_51 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82321664643159 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (440889517129 / 20000000000000 : ℝ))
      (E := (cell13104 ⟨51, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82321664643159 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (440889517129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_52 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (20571999695073 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204451575659 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨52, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (20571999695073 / 25000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204451575659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_53 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41127178050939 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (440891125199 / 20000000000000 : ℝ))
      (E := (cell13104 ⟨53, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41127178050939 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (440891125199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_54 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82220736580013 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204459614949 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨54, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82220736580013 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204459614949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_55 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82187140186933 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (220446365697 / 10000000000000 : ℝ))
      (E := (cell13104 ⟨55, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82187140186933 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (220446365697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_56 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (82153566895013 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204467689003 / 100000000000000 : ℝ))
      (E := (cell13104 ⟨56, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (82153566895013 / 100000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (2204467689003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_57 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (41060008338383 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551117911923 / 25000000000000 : ℝ))
      (E := (cell13104 ⟨57, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (41060008338383 / 50000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (551117911923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_58 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (2052162237621 / 2500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (275559463277 / 12500000000000 : ℝ))
      (E := (cell13104 ⟨58, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (2052162237621 / 2500000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (275559463277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13104_59 : CellCertificate 13104 (43786907336771 / 500000000000000 : ℝ) (320577164036907 / 200000000000000000 : ℝ) (323539066109107 / 10000000000000000 : ℝ)
    (cell13104 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · norm_num [cell13104]
  · have h := gap_lower (n := 13104) (a := (4102649267601 / 5000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102239841219 / 50000000000000 : ℝ))
      (E := (cell13104 ⟨59, by decide⟩).energy) (xi := (323539066109107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13104 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13104) (a := (4102649267601 / 5000000000000 : ℝ)) (b := (157130836161 / 100000000000000 : ℝ)) (q := (1102239841219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13104]

theorem cert13105_40 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (2584172295933 / 3125000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551072866317 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨40, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (2584172295933 / 3125000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551072866317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_41 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82659590701939 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102147750123 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨41, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82659590701939 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102147750123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_42 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (20656422858703 / 25000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551074875733 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨42, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (20656422858703 / 25000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551074875733 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_43 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82591815638989 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204303530903 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨43, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82591815638989 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204303530903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_44 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (8255796328513 / 10000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204307523857 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨44, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (8255796328513 / 10000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204307523857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_45 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (16504826868809 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (275538942373 / 12500000000000 : ℝ))
      (E := (cell13105 ⟨45, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (16504826868809 / 20000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (275538942373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_46 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82490328786689 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204315574429 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨46, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82490328786689 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204315574429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_47 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41228273292081 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102159784587 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨47, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41228273292081 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102159784587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_48 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (8242278770771 / 10000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204323579837 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨48, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (8242278770771 / 10000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204323579837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_49 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82389052128723 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204327603923 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨49, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82389052128723 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204327603923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_50 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82355339818733 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204331638723 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨50, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82355339818733 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204331638723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_51 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82321650749417 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102167811137 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨51, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82321650749417 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102167811137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_52 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82287984892591 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204339669509 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨52, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82287984892591 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204339669509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_53 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82254342220211 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102171829491 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨53, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82254342220211 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102171829491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_54 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (10277590338047 / 12500000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102173852649 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨54, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (10277590338047 / 12500000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102173852649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_55 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (41093563158661 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102175843249 / 50000000000000 : ℝ))
      (E := (cell13105 ⟨55, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (41093563158661 / 50000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (1102175843249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_56 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82153553031423 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204355716871 / 100000000000000 : ℝ))
      (E := (cell13105 ⟨56, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82153553031423 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (2204355716871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_57 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (10265000352399 / 12500000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (220435973313 / 10000000000000 : ℝ))
      (E := (cell13105 ⟨57, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (10265000352399 / 12500000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (220435973313 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_58 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82086475653277 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551090947527 / 25000000000000 : ℝ))
      (E := (cell13105 ⟨58, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82086475653277 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (551090947527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13105_59 : CellCertificate 13105 (175142367992743 / 2000000000000000 : ℝ) (801381735099847 / 500000000000000000 : ℝ) (64702762206659 / 2000000000000000 : ℝ)
    (cell13105 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · norm_num [cell13105]
  · have h := gap_lower (n := 13105) (a := (82052971506463 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (68886492651 / 3125000000000 : ℝ))
      (E := (cell13105 ⟨59, by decide⟩).energy) (xi := (64702762206659 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13105 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13105) (a := (82052971506463 / 100000000000000 : ℝ)) (b := (78559354183 / 50000000000000 : ℝ)) (q := (68886492651 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13105]

theorem cert13106_40 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41346749755743 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (220417957977 / 10000000000000 : ℝ))
      (E := (cell13106 ⟨40, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41346749755743 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (220417957977 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_41 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41329788374831 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204183553613 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨41, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41329788374831 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204183553613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_42 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82625677488623 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204187612827 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨42, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82625677488623 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204187612827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_43 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82591801698883 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551047894927 / 25000000000000 : ℝ))
      (E := (cell13106 ⟨43, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82591801698883 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (551047894927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_44 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82557949351103 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204195629329 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨44, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82557949351103 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204195629329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_45 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82524120416091 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440839928463 / 20000000000000 : ℝ))
      (E := (cell13106 ⟨45, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82524120416091 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440839928463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_46 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41245157432401 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440840735133 / 20000000000000 : ℝ))
      (E := (cell13106 ⟨46, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41245157432401 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440840735133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_47 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82456532668339 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204207668359 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨47, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82456532668339 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204207668359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_48 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (16484554759589 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204211677019 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨48, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (16484554759589 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204211677019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_49 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (20597259556253 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102107849573 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨49, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (20597259556253 / 25000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102107849573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_50 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82355325921071 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440843946407 / 20000000000000 : ℝ))
      (E := (cell13106 ⟨50, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82355325921071 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440843946407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_51 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82321636857799 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204223713719 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨51, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82321636857799 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204223713719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_52 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82287971007011 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (68882117473 / 3125000000000 : ℝ))
      (E := (cell13106 ⟨52, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82287971007011 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (68882117473 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_53 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (41127164170333 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102115873417 / 50000000000000 : ℝ))
      (E := (cell13106 ⟨53, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (41127164170333 / 50000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (1102115873417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_54 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (4111035441543 / 5000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204235791423 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨54, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (4111035441543 / 5000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204235791423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_55 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82187112449831 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204239770941 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨55, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82187112449831 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204239770941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_56 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (2567298099061 / 3125000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204243799677 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨56, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (2567298099061 / 3125000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204243799677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_57 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (16423997792747 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204247814347 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨57, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (16423997792747 / 20000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204247814347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_58 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82086461803831 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204251869781 / 100000000000000 : ℝ))
      (E := (cell13106 ⟨58, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82086461803831 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (2204251869781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13106_59 : CellCertificate 13106 (437842768517329 / 5000000000000000 : ℝ) (400660284722909 / 250000000000000000 : ℝ) (161744279964197 / 5000000000000000 : ℝ)
    (cell13106 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · norm_num [cell13106]
  · have h := gap_lower (n := 13106) (a := (82052957663023 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440851168601 / 20000000000000 : ℝ))
      (E := (cell13106 ⟨59, by decide⟩).energy) (xi := (161744279964197 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13106 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13106) (a := (82052957663023 / 100000000000000 : ℝ)) (b := (157106582449 / 100000000000000 : ℝ)) (q := (440851168601 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13106]

theorem cert13107_40 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82693485555249 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440813538007 / 20000000000000 : ℝ))
      (E := (cell13107 ⟨40, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82693485555249 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (440813538007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_41 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82659562799517 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (137754478847 / 6250000000000 : ℝ))
      (E := (cell13107 ⟨41, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82659562799517 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (137754478847 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_42 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (16525132708913 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (275509464811 / 12500000000000 : ℝ))
      (E := (cell13107 ⟨42, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (16525132708913 / 20000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (275509464811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_43 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82591787760907 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (34438745049 / 1562500000000 : ℝ))
      (E := (cell13107 ⟨43, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82591787760907 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (34438745049 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_44 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (20639483854801 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204083730569 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨44, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (20639483854801 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204083730569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_45 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (10315513311283 / 12500000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102043870707 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨45, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (10315513311283 / 12500000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102043870707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_46 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82490300945043 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204091772669 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨46, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82490300945043 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204091772669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_47 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41228259377321 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102047881657 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨47, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41228259377321 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102047881657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_48 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41211379945153 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204099769971 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨48, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41211379945153 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204099769971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_49 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (3295560972937 / 4000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102051895071 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨49, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (3295560972937 / 4000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102051895071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_50 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (20588828006383 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204107821119 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨50, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (20588828006383 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204107821119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_51 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41160811484151 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204111859983 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨51, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41160811484151 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204111859983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_52 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82287957123553 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204115844537 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨52, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82287957123553 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204115844537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_53 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82254314463241 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (137757493097 / 6250000000000 : ℝ))
      (E := (cell13107 ⟨53, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82254314463241 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (137757493097 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_54 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (10277586869933 / 12500000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204123873323 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨54, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (10277586869933 / 12500000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204123873323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_55 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41093549292229 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102063955149 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨55, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41093549292229 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102063955149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_56 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (41076762655299 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102065968711 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨56, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (41076762655299 / 50000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102065968711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_57 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (20529993777599 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102067975263 / 50000000000000 : ℝ))
      (E := (cell13107 ⟨57, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (20529993777599 / 25000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (1102067975263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_58 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (164172895913 / 200000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204139945233 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨58, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (164172895913 / 200000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204139945233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13107_59 : CellCertificate 13107 (109457404743421 / 1250000000000000 : ℝ) (1602518826256083 / 1000000000000000000 : ℝ) (323463312793413 / 10000000000000000 : ℝ)
    (cell13107 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · norm_num [cell13107]
  · have h := gap_lower (n := 13107) (a := (82052943821697 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204143976191 / 100000000000000 : ℝ))
      (E := (cell13107 ⟨59, by decide⟩).energy) (xi := (323463312793413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13107 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13107) (a := (82052943821697 / 100000000000000 : ℝ)) (b := (39273614603 / 25000000000000 : ℝ)) (q := (2204143976191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13107]

theorem cert13108_40 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (10336683950143 / 12500000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550988949017 / 25000000000000 : ℝ))
      (E := (cell13108 ⟨40, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (10336683950143 / 12500000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550988949017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_41 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (82659548851503 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203959824069 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨41, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (82659548851503 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203959824069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_42 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (82625649602637 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203963819917 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨42, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (82625649602637 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203963819917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_43 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (4129588691253 / 5000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203967841189 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨43, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (4129588691253 / 5000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203967841189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_44 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (82557921489433 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203971827581 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨44, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (82557921489433 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203971827581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_45 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (16504818513313 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203975895187 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨45, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (16504818513313 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203975895187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_46 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (8249028702741 / 10000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (440795973089 / 20000000000000 : ℝ))
      (E := (cell13108 ⟨46, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (8249028702741 / 10000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (440795973089 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_47 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (8245650484307 / 10000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203983912993 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨47, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (8245650484307 / 10000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203983912993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_48 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (82422745984791 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (220398791767 / 10000000000000 : ℝ))
      (E := (cell13108 ⟨48, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (82422745984791 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (220398791767 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_49 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (41194505211981 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550997983977 / 25000000000000 : ℝ))
      (E := (cell13108 ⟨49, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (41194505211981 / 50000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (550997983977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_50 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (20588824533029 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203995964999 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨50, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (20588824533029 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203995964999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_51 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (2572550283779 / 3125000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203999942979 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨51, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (2572550283779 / 3125000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2203999942979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_52 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (10285992905277 / 12500000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1102001992391 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨52, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (10285992905277 / 12500000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1102001992391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_53 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (2570446893373 / 3125000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2204008028049 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨53, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (2570446893373 / 3125000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2204008028049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_54 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (82220681090187 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2204012010117 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨54, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (82220681090187 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2204012010117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_55 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (82187084721203 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (551004011359 / 25000000000000 : ℝ))
      (E := (cell13108 ⟨55, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (82187084721203 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (551004011359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_56 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (82153511453361 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2204020070949 / 100000000000000 : ℝ))
      (E := (cell13108 ⟨56, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (82153511453361 / 100000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (2204020070949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_57 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (20529990314793 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275503010311 / 12500000000000 : ℝ))
      (E := (cell13108 ⟨57, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (20529990314793 / 25000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (275503010311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_58 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (16417286822257 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (88161123027 / 4000000000000 : ℝ))
      (E := (cell13108 ⟨58, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (16417286822257 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (88161123027 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13108_59 : CellCertificate 13108 (5472705891881 / 62500000000000 : ℝ) (801198266144381 / 500000000000000000 : ℝ) (80859517406841 / 2500000000000000 : ℝ)
    (cell13108 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · norm_num [cell13108]
  · have h := gap_lower (n := 13108) (a := (16410585996497 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1102016052581 / 50000000000000 : ℝ))
      (E := (cell13108 ⟨59, by decide⟩).energy) (xi := (80859517406841 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13108 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13108) (a := (16410585996497 / 20000000000000 : ℝ)) (b := (39270584063 / 25000000000000 : ℝ)) (q := (1102016052581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13108]

theorem cert13109_40 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (8269345764917 / 10000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101921978327 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨40, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (8269345764917 / 10000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101921978327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_41 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82659534905619 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (440769596471 / 20000000000000 : ℝ))
      (E := (cell13109 ⟨41, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82659534905619 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (440769596471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_42 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82625635662839 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550962993987 / 25000000000000 : ℝ))
      (E := (cell13109 ⟨42, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82625635662839 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550962993987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_43 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82591759891343 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203855995011 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨43, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82591759891343 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203855995011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_44 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82557907561791 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (55096499481 / 2500000000000 : ℝ))
      (E := (cell13109 ⟨44, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82557907561791 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (55096499481 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_45 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82524078644993 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203864044731 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨45, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82524078644993 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203864044731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_46 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82490273111903 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (55096700323 / 2500000000000 : ℝ))
      (E := (cell13109 ⟨46, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82490273111903 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (55096700323 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_47 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (10307061366703 / 12500000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550968014611 / 25000000000000 : ℝ))
      (E := (cell13109 ⟨47, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (10307061366703 / 12500000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550968014611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_48 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (412113660407 / 500000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (275484507643 / 12500000000000 : ℝ))
      (E := (cell13109 ⟨48, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (412113660407 / 500000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (275484507643 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_49 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41194498263311 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (44077601549 / 2000000000000 : ℝ))
      (E := (cell13109 ⟨49, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41194498263311 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (44077601549 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_50 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (41177642120411 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (440776820931 / 20000000000000 : ℝ))
      (E := (cell13109 ⟨50, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (41177642120411 / 50000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (440776820931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_51 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (3292863807827 / 4000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203888139839 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨51, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (3292863807827 / 4000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203888139839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_52 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82287929362999 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550973030201 / 25000000000000 : ℝ))
      (E := (cell13109 ⟨52, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82287929362999 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550973030201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_53 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82254286714751 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203896162323 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨53, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82254286714751 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203896162323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_54 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (20555166805757 / 25000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203900142689 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨54, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (20555166805757 / 25000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203900142689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_55 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82187070860067 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203904176351 / 100000000000000 : ℝ))
      (E := (cell13109 ⟨55, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82187070860067 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (2203904176351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_56 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (82153497598241 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (34436065629 / 1562500000000 : ℝ))
      (E := (cell13109 ⟨56, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (82153497598241 / 100000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (34436065629 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_57 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (16423989482013 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220391221023 / 10000000000000 : ℝ))
      (E := (cell13109 ⟨57, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (16423989482013 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (220391221023 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_58 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (16417284053637 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550979065277 / 25000000000000 : ℝ))
      (E := (cell13109 ⟨58, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (16417284053637 / 20000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (550979065277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13109_59 : CellCertificate 13109 (109450831411819 / 1250000000000000 : ℝ) (1602274256985399 / 1000000000000000000 : ℝ) (323412830429257 / 10000000000000000 : ℝ)
    (cell13109 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · norm_num [cell13109]
  · have h := gap_lower (n := 13109) (a := (20513229036347 / 25000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101960114957 / 50000000000000 : ℝ))
      (E := (cell13109 ⟨59, by decide⟩).energy) (xi := (323412830429257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13109 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13109) (a := (20513229036347 / 25000000000000 : ℝ)) (b := (15707021597 / 10000000000000 : ℝ)) (q := (1101960114957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13109]

theorem cert13110_40 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (646042528901 / 781250000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203732113007 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨40, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (646042528901 / 781250000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203732113007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_41 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41329760480933 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203736136409 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨41, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41329760480933 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203736136409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_42 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (8262562172517 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550935031937 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨42, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (8262562172517 / 10000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550935031937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_43 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82591745959753 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550936036151 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨43, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82591745959753 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550936036151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_44 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (20639473409069 / 25000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (137734261597 / 6250000000000 : ℝ))
      (E := (cell13110 ⟨44, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (20639473409069 / 25000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (137734261597 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_45 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82524064725547 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203752190049 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨45, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82524064725547 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203752190049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_46 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41245129599261 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101878107547 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨46, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41245129599261 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101878107547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_47 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41228238513151 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203760199669 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨47, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41228238513151 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203760199669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_48 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82422718180133 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101882129683 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨48, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82422718180133 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101882129683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_49 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (16477796526281 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550942068441 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨49, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (16477796526281 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550942068441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_50 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (1647105407033 / 2000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203772299107 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨50, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (1647105407033 / 2000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203772299107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_51 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82321581312543 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (275472034179 / 12500000000000 : ℝ))
      (E := (cell13110 ⟨51, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82321581312543 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (275472034179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_52 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82287915485903 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (275472538959 / 12500000000000 : ℝ))
      (E := (cell13110 ⟨52, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82287915485903 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (275472538959 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_53 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (16450854568737 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550946087867 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨53, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (16450854568737 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550946087867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_54 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82220653357987 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203788330157 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨54, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82220653357987 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203788330157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_55 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82187057001047 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203792362187 / 100000000000000 : ℝ))
      (E := (cell13110 ⟨55, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82187057001047 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (2203792362187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_56 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (41076741872619 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101898192253 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨56, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (41076741872619 / 50000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101898192253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_57 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (82119933563073 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (110190019647 / 5000000000000 : ℝ))
      (E := (cell13110 ⟨57, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (82119933563073 / 100000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (110190019647 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_58 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (51304004017 / 62500000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550951095779 / 25000000000000 : ℝ))
      (E := (cell13110 ⟨58, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (51304004017 / 62500000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (550951095779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13110_59 : CellCertificate 13110 (875580363727263 / 10000000000000000 : ℝ) (801076000170861 / 500000000000000000 : ℝ) (161693797599053 / 5000000000000000 : ℝ)
    (cell13110 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · norm_num [cell13110]
  · have h := gap_lower (n := 13110) (a := (16410580462081 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101904204841 / 50000000000000 : ℝ))
      (E := (cell13110 ⟨59, by decide⟩).energy) (xi := (161693797599053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13110 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13110) (a := (16410580462081 / 20000000000000 : ℝ)) (b := (31411619513 / 20000000000000 : ℝ)) (q := (1101904204841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13110]

theorem cert13111_40 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (1292084839869 / 1562500000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440724064783 / 20000000000000 : ℝ))
      (E := (cell13111 ⟨40, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (1292084839869 / 1562500000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440724064783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_41 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (82659507020243 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203624345041 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨41, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (82659507020243 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203624345041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_42 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (8262560778963 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (275453541769 / 12500000000000 : ℝ))
      (E := (cell13111 ⟨42, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (8262560778963 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (275453541769 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_43 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (82591732030291 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (88145293953 / 4000000000000 : ℝ))
      (E := (cell13111 ⟨43, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (82591732030291 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (88145293953 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_44 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (82557879712887 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203636387637 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨44, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (82557879712887 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203636387637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_45 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (82524050808227 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101820195021 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨45, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (82524050808227 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101820195021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_46 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41245122643633 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203644413043 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨46, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41245122643633 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203644413043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_47 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (16491292624221 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203648395619 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨47, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (16491292624221 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203648395619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_48 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (8242270428099 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101826226681 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨48, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (8242270428099 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101826226681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_49 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (8238896873831 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440731293171 / 20000000000000 : ℝ))
      (E := (cell13111 ⟨49, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (8238896873831 / 10000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440731293171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_50 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (82355256464599 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101830244669 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨50, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (82355256464599 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101830244669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_51 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (20580391857883 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (275458057731 / 12500000000000 : ℝ))
      (E := (cell13111 ⟨51, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (20580391857883 / 25000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (275458057731 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_52 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41143950805463 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203668498319 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨52, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41143950805463 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203668498319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_53 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (82254258974737 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203672536393 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨53, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (82254258974737 / 100000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203672536393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_54 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (16444127899013 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550919128351 / 25000000000000 : ℝ))
      (E := (cell13111 ⟨54, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (16444127899013 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550919128351 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_55 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (5136690196509 / 6250000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440736108761 / 20000000000000 : ℝ))
      (E := (cell13111 ⟨55, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (5136690196509 / 6250000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440736108761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_56 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (1643069397887 / 2000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203684564539 / 100000000000000 : ℝ))
      (E := (cell13111 ⟨56, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (1643069397887 / 2000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (2203684564539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_57 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (16423983943639 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440737714287 / 20000000000000 : ℝ))
      (E := (cell13111 ⟨57, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (16423983943639 / 20000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (440737714287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_58 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (10260799073541 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101846309663 / 50000000000000 : ℝ))
      (E := (cell13111 ⟨58, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (10260799073541 / 12500000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (1101846309663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13111_59 : CellCertificate 13111 (875554079998209 / 10000000000000000 : ℝ) (1602029762353459 / 1000000000000000000 : ℝ) (323362363932921 / 10000000000000000 : ℝ)
    (cell13111 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · norm_num [cell13111]
  · have h := gap_lower (n := 13111) (a := (41026444238767 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550924161117 / 25000000000000 : ℝ))
      (E := (cell13111 ⟨59, by decide⟩).energy) (xi := (323362363932921 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13111 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13111) (a := (41026444238767 / 50000000000000 : ℝ)) (b := (157045981037 / 100000000000000 : ℝ)) (q := (550924161117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13111]

theorem cert13112_40 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41346707903017 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101754265297 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨40, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41346707903017 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101754265297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_41 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (20664873270187 / 25000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101756274723 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨41, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (20664873270187 / 25000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101756274723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_42 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41312796928109 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (275439567041 / 12500000000000 : ℝ))
      (E := (cell13112 ⟨42, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41312796928109 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (275439567041 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_43 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82591718102957 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203520548819 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨43, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82591718102957 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203520548819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_44 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41278932895813 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101762292747 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨44, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41278932895813 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101762292747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_45 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82524036893033 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (220352858581 / 10000000000000 : ℝ))
      (E := (cell13112 ⟨45, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82524036893033 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (220352858581 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_46 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (16498046275627 / 20000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203532606767 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨46, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (16498046275627 / 20000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203532606767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_47 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82456449218031 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (275442080787 / 12500000000000 : ℝ))
      (E := (cell13112 ⟨47, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82456449218031 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (275442080787 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_48 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82422690383969 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203540643137 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨48, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82422690383969 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203540643137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_49 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82388954847337 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550886163431 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨49, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82388954847337 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550886163431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_50 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82355242579669 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550887168837 / 25000000000000 : ℝ))
      (E := (cell13112 ⟨50, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82355242579669 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (550887168837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_51 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (64313713713 / 78125000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (34430511017 / 1562500000000 : ℝ))
      (E := (cell13112 ⟨51, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (64313713713 / 78125000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (34430511017 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_52 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82287887738067 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (440711347963 / 20000000000000 : ℝ))
      (E := (cell13112 ⟨52, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82287887738067 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (440711347963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_53 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (20563561276977 / 25000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203560717099 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨53, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (20563561276977 / 25000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203560717099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_54 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82220625634259 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (44071295031 / 2000000000000 : ℝ))
      (E := (cell13112 ⟨54, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82220625634259 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (44071295031 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_55 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41093514644679 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203568780343 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨55, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41093514644679 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203568780343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_56 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (41076728022789 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203572799517 / 100000000000000 : ℝ))
      (E := (cell13112 ⟨56, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (41076728022789 / 50000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (2203572799517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_57 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (82119905875433 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101788402449 / 50000000000000 : ℝ))
      (E := (cell13112 ⟨57, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (82119905875433 / 100000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (1101788402449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_58 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (8208637875157 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (137723799507 / 6250000000000 : ℝ))
      (E := (cell13112 ⟨58, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (8208637875157 / 10000000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (137723799507 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13112_59 : CellCertificate 13112 (87552780010651 / 1000000000000000 : ℝ) (1601907543016341 / 1000000000000000000 : ℝ) (80834284158179 / 2500000000000000 : ℝ)
    (cell13112 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · norm_num [cell13112]
  · have h := gap_lower (n := 13112) (a := (10256609330847 / 12500000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (34431012747 / 1562500000000 : ℝ))
      (E := (cell13112 ⟨59, by decide⟩).energy) (xi := (80834284158179 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13112 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13112) (a := (10256609330847 / 12500000000000 : ℝ)) (b := (31406773277 / 20000000000000 : ℝ)) (q := (34431012747 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13112]

theorem cert13113_40 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41346700931291 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550849183261 / 25000000000000 : ℝ))
      (E := (cell13113 ⟨40, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41346700931291 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550849183261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_41 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (82659479143383 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101700374811 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨41, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (82659479143383 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101700374811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_42 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (41312789962467 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (220340479311 / 10000000000000 : ℝ))
      (E := (cell13113 ⟨42, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (41312789962467 / 50000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (220340479311 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_43 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (82591704177749 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550852200861 / 25000000000000 : ℝ))
      (E := (cell13113 ⟨43, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (82591704177749 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550852200861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_44 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (8255785187249 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203412838007 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨44, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (8255785187249 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203412838007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_45 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (20631005744991 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203416836257 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨45, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (20631005744991 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203416836257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_46 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (82490217471127 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440684171039 / 20000000000000 : ℝ))
      (E := (cell13113 ⟨46, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (82490217471127 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (440684171039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_47 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (82456435317081 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203424892749 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨47, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (82456435317081 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203424892749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_48 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (8242267648907 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (137714305479 / 6250000000000 : ℝ))
      (E := (cell13113 ⟨48, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (8242267648907 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (137714305479 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_49 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (16477788191697 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (220343289637 / 10000000000000 : ℝ))
      (E := (cell13113 ⟨49, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (16477788191697 / 20000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (220343289637 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_50 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (4117761434843 / 5000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203436916157 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨50, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (4117761434843 / 5000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203436916157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_51 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (20580384918967 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550860236027 / 25000000000000 : ℝ))
      (E := (cell13113 ⟨51, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (20580384918967 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550860236027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_52 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (1285748029177 / 1562500000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550861244273 / 25000000000000 : ℝ))
      (E := (cell13113 ⟨52, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (1285748029177 / 1562500000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (550861244273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_53 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (20563557810799 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101724476339 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨53, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (20563557810799 / 25000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101724476339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_54 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (8222061177557 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101726492739 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨54, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (8222061177557 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101726492739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_55 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (82187015436687 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101728506333 / 50000000000000 : ℝ))
      (E := (cell13113 ⟨55, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (82187015436687 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (1101728506333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_56 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (82153442198921 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203461030279 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨56, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (82153442198921 / 100000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203461030279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_57 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (2566246626087 / 3125000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203465034147 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨57, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (2566246626087 / 3125000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203465034147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_58 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (3283454596677 / 4000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203469079103 / 100000000000000 : ℝ))
      (E := (cell13113 ⟨58, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (3283454596677 / 4000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (2203469079103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13113_59 : CellCertificate 13113 (875501524051283 / 10000000000000000 : ℝ) (16017853423261 / 10000000000000000 : ℝ) (40413989162063 / 1250000000000000 : ℝ)
    (cell13113 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · norm_num [cell13113]
  · have h := gap_lower (n := 13113) (a := (8205286081813 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (275434130271 / 12500000000000 : ℝ))
      (E := (cell13113 ⟨59, by decide⟩).energy) (xi := (40413989162063 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13113 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13113) (a := (8205286081813 / 10000000000000 : ℝ)) (b := (157021753609 / 100000000000000 : ℝ)) (q := (275434130271 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13113]

theorem cert13114_40 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82693387921259 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550821247513 / 25000000000000 : ℝ))
      (E := (cell13114 ⟨40, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82693387921259 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550821247513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_41 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16531893041629 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101644502191 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨41, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16531893041629 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101644502191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_42 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (41312782997889 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101646522833 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨42, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (41312782997889 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101646522833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_43 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (20647922563667 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203297053843 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨43, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (20647922563667 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203297053843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_44 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82557837955479 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (275412635787 / 12500000000000 : ℝ))
      (E := (cell13114 ⟨44, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82557837955479 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (275412635787 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_45 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82524009069019 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203305082481 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨45, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82524009069019 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203305082481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_46 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82490203566243 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (11016545497 / 500000000000 : ℝ))
      (E := (cell13114 ⟨46, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82490203566243 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (11016545497 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_47 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82456421418253 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203313134981 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨47, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82456421418253 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203313134981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_48 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82422662596293 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220331712797 / 10000000000000 : ℝ))
      (E := (cell13114 ⟨48, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82422662596293 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220331712797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_49 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16477785414351 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101660567397 / 50000000000000 : ℝ))
      (E := (cell13114 ⟨49, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16477785414351 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (1101660567397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_50 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (8235521481617 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550831288187 / 25000000000000 : ℝ))
      (E := (cell13114 ⟨50, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (8235521481617 / 10000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (550831288187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_51 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (16464305160243 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203329178911 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨51, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (16464305160243 / 20000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203329178911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_52 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (41143929999353 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (275416651269 / 12500000000000 : ℝ))
      (E := (cell13114 ⟨52, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (41143929999353 / 50000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (275416651269 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_53 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82254217380601 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203337243133 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨53, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82254217380601 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203337243133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_54 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82220597918997 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203341215191 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨54, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82220597918997 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203341215191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_55 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82187001586131 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (88133809631 / 4000000000000 : ℝ))
      (E := (cell13114 ⟨55, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82187001586131 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (88133809631 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_56 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82153428354377 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203349256829 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨56, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82153428354377 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203349256829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_57 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (10264984774531 / 12500000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220335331837 / 10000000000000 : ℝ))
      (E := (cell13114 ⟨57, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (10264984774531 / 12500000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (220335331837 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_58 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (82086351084393 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (137709831417 / 6250000000000 : ℝ))
      (E := (cell13114 ⟨58, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (82086351084393 / 100000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (137709831417 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13114_59 : CellCertificate 13114 (27358601619739 / 312500000000000 : ℝ) (1601663160278467 / 1000000000000000000 : ℝ) (323286693923297 / 10000000000000000 : ℝ)
    (cell13114 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · norm_num [cell13114]
  · have h := gap_lower (n := 13114) (a := (20513211747899 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203361323549 / 100000000000000 : ℝ))
      (E := (cell13114 ⟨59, by decide⟩).energy) (xi := (323286693923297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13114 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13114) (a := (20513211747899 / 25000000000000 : ℝ)) (b := (39252410677 / 25000000000000 : ℝ)) (q := (2203361323549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13114]

theorem cert13115_40 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (16538674796413 / 20000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203173301619 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨40, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (16538674796413 / 20000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203173301619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_41 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (20664862818759 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550794328431 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨41, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (20664862818759 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550794328431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_42 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (20656388017187 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550795323499 / 25000000000000 : ℝ))
      (E := (cell13115 ⟨42, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (20656388017187 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (550795323499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_43 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82591676333713 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101592679437 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨43, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82591676333713 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101592679437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_44 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41278912020297 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203189330359 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨44, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41278912020297 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203189330359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_45 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41261997580099 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440638676677 / 20000000000000 : ℝ))
      (E := (cell13115 ⟨45, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41261997580099 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440638676677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_46 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41245094831741 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203197398309 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨46, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41245094831741 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203197398309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_47 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82456407521547 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (34425021453 / 1562500000000 : ℝ))
      (E := (cell13115 ⟨47, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82456407521547 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (34425021453 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_48 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82422648705637 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203205423029 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨48, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82422648705637 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203205423029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_49 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (10298614148393 / 12500000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101604713999 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨49, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (10298614148393 / 12500000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101604713999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_50 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (25736000293 / 31250000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203213444141 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨50, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (25736000293 / 31250000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203213444141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_51 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82321511928681 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101608734269 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨51, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82321511928681 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101608734269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_52 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82287846132203 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101610749031 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨52, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82287846132203 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101610749031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_53 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82254203520123 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (55080636757 / 2500000000000 : ℝ))
      (E := (cell13115 ⟨53, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82254203520123 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (55080636757 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_54 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82220584064541 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101614749901 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨54, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82220584064541 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101614749901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_55 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82186987737691 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440646704761 / 20000000000000 : ℝ))
      (E := (cell13115 ⟨55, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82186987737691 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (440646704761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_56 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (20538353627987 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101618769163 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨56, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (20538353627987 / 25000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101618769163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_57 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (41059932179913 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (275405192399 / 12500000000000 : ℝ))
      (E := (cell13115 ⟨57, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (41059932179913 / 50000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (275405192399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_58 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82086337253973 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203245581237 / 100000000000000 : ℝ))
      (E := (cell13115 ⟨58, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82086337253973 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (2203245581237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13115_59 : CellCertificate 13115 (218862245861681 / 2500000000000000 : ℝ) (1601540996869179 / 1000000000000000000 : ℝ) (323261478512109 / 10000000000000000 : ℝ)
    (cell13115 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · norm_num [cell13115]
  · have h := gap_lower (n := 13115) (a := (82052833167173 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101624800359 / 50000000000000 : ℝ))
      (E := (cell13115 ⟨59, by decide⟩).energy) (xi := (323261478512109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13115 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13115) (a := (82052833167173 / 100000000000000 : ℝ)) (b := (156997533683 / 100000000000000 : ℝ)) (q := (1101624800359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13115]

theorem cert13116_40 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82693360044999 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203061608961 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨40, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82693360044999 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203061608961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_41 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41329718672027 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203065618841 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨41, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41329718672027 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203065618841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_42 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20656384535961 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (275383699617 / 12500000000000 : ℝ))
      (E := (cell13116 ⟨42, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20656384535961 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (275383699617 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_43 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82591662414883 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101536829841 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨43, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82591662414883 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101536829841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_44 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82557810127833 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101538814541 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨44, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82557810127833 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101538814541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_45 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82523981253501 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550770420017 / 25000000000000 : ℝ))
      (E := (cell13116 ⟨45, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82523981253501 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550770420017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_46 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20622543940711 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203085692999 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨46, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20622543940711 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203085692999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_47 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82456393626963 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101544832867 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨47, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82456393626963 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101544832867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_48 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82422634817103 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203093713869 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨48, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82422634817103 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203093713869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_49 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (41194449652327 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101548858491 / 50000000000000 : ℝ))
      (E := (cell13116 ⟨49, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (41194449652327 / 50000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (1101548858491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_50 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82355187061149 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550775432829 / 25000000000000 : ℝ))
      (E := (cell13116 ⟨50, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82355187061149 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (550775432829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_51 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (10290187257283 / 12500000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203105753951 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨51, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (10290187257283 / 12500000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203105753951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_52 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (10285979033477 / 12500000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203109781757 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨52, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (10285979033477 / 12500000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203109781757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_53 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82254189661761 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440622762279 / 20000000000000 : ℝ))
      (E := (cell13116 ⟨53, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82254189661761 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440622762279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_54 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82220570212199 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440623567863 / 20000000000000 : ℝ))
      (E := (cell13116 ⟨54, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82220570212199 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (440623567863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_55 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20546743472841 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (17624974421 / 800000000000 : ℝ))
      (E := (cell13116 ⟨55, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20546743472841 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (17624974421 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_56 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82153400671633 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203125874773 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨56, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82153400671633 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203125874773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_57 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (20529962631379 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (8605976071 / 390625000000 : ℝ))
      (E := (cell13116 ⟨57, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (20529962631379 / 25000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (8605976071 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_58 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (641299401763 / 781250000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203133855593 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨58, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (641299401763 / 781250000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203133855593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13116_59 : CellCertificate 13116 (87542271889563 / 1000000000000000 : ℝ) (160141885209397 / 100000000000000000 : ℝ) (80809066765489 / 2500000000000000 : ℝ)
    (cell13116 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · norm_num [cell13116]
  · have h := gap_lower (n := 13116) (a := (82052819344861 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203137873677 / 100000000000000 : ℝ))
      (E := (cell13116 ⟨59, by decide⟩).energy) (xi := (80809066765489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13116 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13116) (a := (82052819344861 / 100000000000000 : ℝ)) (b := (39246356633 / 25000000000000 : ℝ)) (q := (2203137873677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13116]

theorem cert13117_40 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (4134667305503 / 5000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202949912079 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨40, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (4134667305503 / 5000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202949912079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_41 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41329711707599 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (440590783947 / 20000000000000 : ℝ))
      (E := (cell13117 ⟨41, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41329711707599 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (440590783947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_42 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41312762110533 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202957954487 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨42, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41312762110533 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202957954487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_43 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41295824249089 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (550740489067 / 25000000000000 : ℝ))
      (E := (cell13117 ⟨43, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41295824249089 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (550740489067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_44 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (20639449054299 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202965982463 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨44, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (20639449054299 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202965982463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_45 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (82523967348927 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (220296997253 / 10000000000000 : ℝ))
      (E := (cell13117 ⟨45, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (82523967348927 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (220296997253 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_46 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (10311270233041 / 12500000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (550743495867 / 25000000000000 : ℝ))
      (E := (cell13117 ⟨46, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (10311270233041 / 12500000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (550743495867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_47 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (164912759469 / 200000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (275372251651 / 12500000000000 : ℝ))
      (E := (cell13117 ⟨47, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (164912759469 / 200000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (275372251651 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_48 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (643926726021 / 781250000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101491029733 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨48, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (643926726021 / 781250000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101491029733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_49 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41194442712141 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202986060749 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨49, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41194442712141 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202986060749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_50 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (321699895261 / 390625000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202990073297 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨50, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (321699895261 / 390625000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202990073297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_51 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (16464296837993 / 20000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202994094193 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨51, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (16464296837993 / 20000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2202994094193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_52 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41143909202773 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101499060153 / 50000000000000 : ℝ))
      (E := (cell13117 ⟨52, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41143909202773 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (1101499060153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_53 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (16450835161103 / 20000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (440600417841 / 20000000000000 : ℝ))
      (E := (cell13117 ⟨53, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (16450835161103 / 20000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (440600417841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_54 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (20555139090493 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203006115501 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨54, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (20555139090493 / 25000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203006115501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_55 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (5136685002947 / 6250000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (220301013637 / 10000000000000 : ℝ))
      (E := (cell13117 ⟨55, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (5136685002947 / 6250000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (220301013637 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_56 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (8215338683343 / 10000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203014147847 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨56, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (8215338683343 / 10000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203014147847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_57 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41059918346659 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203018204949 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨57, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41059918346659 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203018204949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_58 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (41043154799733 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203022184949 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨58, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (41043154799733 / 50000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203022184949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13117_59 : CellCertificate 13117 (175079291635497 / 2000000000000000 : ℝ) (50040522685893 / 31250000000000000 : ℝ) (6464221191437 / 200000000000000 : ℝ)
    (cell13117 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · norm_num [cell13117]
  · have h := gap_lower (n := 13117) (a := (82052805524659 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203026201661 / 100000000000000 : ℝ))
      (E := (cell13117 ⟨59, by decide⟩).energy) (xi := (6464221191437 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13117 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13117) (a := (82052805524659 / 100000000000000 : ℝ)) (b := (31394664251 / 20000000000000 : ℝ)) (q := (2203026201661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13117]

theorem cert13118_40 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82693332177249 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202838269759 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨40, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82693332177249 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202838269759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_41 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82659409488469 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202842275217 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨41, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82659409488469 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202842275217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_42 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41312755150207 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101423124491 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨42, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41312755150207 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101423124491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_43 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41295817291799 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (220285030749 / 10000000000000 : ℝ))
      (E := (cell13118 ⟨43, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41295817291799 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (220285030749 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_44 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41278891154341 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (17622834653 / 800000000000 : ℝ))
      (E := (cell13118 ⟨44, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41278891154341 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (17622834653 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_45 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (20630988361619 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202858319677 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨45, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (20630988361619 / 25000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202858319677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_46 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41245073983967 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202862328647 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨46, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41245073983967 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202862328647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_47 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41228182922079 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440573271293 / 20000000000000 : ℝ))
      (E := (cell13118 ⟨47, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41228182922079 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440573271293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_48 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82422607046393 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202870341873 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨48, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82422607046393 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202870341873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_49 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (8238887154603 / 10000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202874400299 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨49, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (8238887154603 / 10000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202874400299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_50 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82355159314601 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (275359801383 / 12500000000000 : ℝ))
      (E := (cell13118 ⟨50, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82355159314601 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (275359801383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_51 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82321470323783 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202882430221 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨51, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82321470323783 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202882430221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_52 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82287804545391 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101443227321 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨52, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82287804545391 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101443227321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_53 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (10281770243923 / 12500000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202890480987 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨53, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (10281770243923 / 12500000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202890480987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_54 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82220542513859 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202894446591 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨54, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82220542513859 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202894446591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_55 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82186946205053 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440579693181 / 20000000000000 : ℝ))
      (E := (cell13118 ⟨55, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82186946205053 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (440579693181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_56 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (4107668649867 / 5000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (550725633759 / 25000000000000 : ℝ))
      (E := (cell13118 ⟨56, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (4107668649867 / 5000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (550725633759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_57 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (641561116119 / 781250000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202906531513 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨57, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (641561116119 / 781250000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202906531513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_58 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (82086295775379 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101455284653 / 50000000000000 : ℝ))
      (E := (cell13118 ⟨58, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (82086295775379 / 100000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (1101455284653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13118_59 : CellCertificate 13118 (87537020129141 / 1000000000000000 : ℝ) (1601174618428737 / 1000000000000000000 : ℝ) (323185856040807 / 10000000000000000 : ℝ)
    (cell13118 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · norm_num [cell13118]
  · have h := gap_lower (n := 13118) (a := (41026395853283 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202914584671 / 100000000000000 : ℝ))
      (E := (cell13118 ⟨59, by decide⟩).energy) (xi := (323185856040807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13118 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13118) (a := (41026395853283 / 50000000000000 : ℝ)) (b := (156961217851 / 100000000000000 : ℝ)) (q := (2202914584671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13118]

theorem cert13119_40 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (16538663649313 / 20000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (137670413951 / 6250000000000 : ℝ))
      (E := (cell13119 ⟨40, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (16538663649313 / 20000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (137670413951 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_41 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (16531879112773 / 20000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550682656619 / 25000000000000 : ℝ))
      (E := (cell13119 ⟨41, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (16531879112773 / 20000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (550682656619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_42 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41312748190943 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202734656923 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨42, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41312748190943 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202734656923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_43 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41295810335571 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220273865449 / 10000000000000 : ℝ))
      (E := (cell13119 ⟨43, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41295810335571 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220273865449 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_44 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (20639442100573 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202742676567 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨44, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (20639442100573 / 25000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202742676567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_45 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82523939546147 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440549332521 / 20000000000000 : ℝ))
      (E := (cell13119 ⟨45, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82523939546147 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440549332521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_46 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82490134073661 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202750669607 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨46, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82490134073661 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202750669607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_47 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (2576760998623 / 3125000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (137672168469 / 6250000000000 : ℝ))
      (E := (cell13119 ⟨47, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (2576760998623 / 3125000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (137672168469 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_48 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41211296582109 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220275873801 / 10000000000000 : ℝ))
      (E := (cell13119 ⟨48, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41211296582109 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (220275873801 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_49 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (10298607208737 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202762735633 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨49, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (10298607208737 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202762735633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_50 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (10294393180563 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440553348923 / 20000000000000 : ℝ))
      (E := (cell13119 ⟨50, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (10294393180563 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440553348923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_51 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41160728229859 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440554152407 / 20000000000000 : ℝ))
      (E := (cell13119 ⟨51, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41160728229859 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440554152407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_52 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82287790687353 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440554956953 / 20000000000000 : ℝ))
      (E := (cell13119 ⟨52, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82287790687353 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (440554956953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_53 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (10281768512421 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (275347351183 / 12500000000000 : ℝ))
      (E := (cell13119 ⟨53, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (10281768512421 / 12500000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (275347351183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_54 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (4111026433393 / 5000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (275347854073 / 12500000000000 : ℝ))
      (E := (cell13119 ⟨54, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (4111026433393 / 5000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (275347854073 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_55 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41093466182533 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202786850369 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨55, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41093466182533 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202786850369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_56 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82153359163361 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202790858853 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨56, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82153359163361 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202790858853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_57 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82119809035257 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101397456527 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨57, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82119809035257 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101397456527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_58 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (41043140976701 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101399445123 / 50000000000000 : ℝ))
      (E := (cell13119 ⟨58, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (41043140976701 / 50000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (1101399445123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13119_59 : CellCertificate 13119 (35013757929461 / 400000000000000 : ℝ) (100065783095637 / 62500000000000000 : ℝ) (323160656467843 / 10000000000000000 : ℝ)
    (cell13119 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · norm_num [cell13119]
  · have h := gap_lower (n := 13119) (a := (82052777890583 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202802904241 / 100000000000000 : ℝ))
      (E := (cell13119 ⟨59, by decide⟩).energy) (xi := (323160656467843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13119 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13119) (a := (82052777890583 / 100000000000000 : ℝ)) (b := (156949116321 / 100000000000000 : ℝ)) (q := (2202802904241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13119]

theorem cert13120_40 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82693304318007 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202614972451 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨40, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82693304318007 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202614972451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_41 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82659381641387 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101309486757 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨41, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82659381641387 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101309486757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_42 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82625482465483 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220262300181 / 10000000000000 : ℝ))
      (E := (cell13120 ⟨42, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82625482465483 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220262300181 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_43 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (10323950845101 / 12500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220262705613 / 10000000000000 : ℝ))
      (E := (cell13120 ⟨43, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (10323950845101 / 12500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220262705613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_44 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (10319719312253 / 12500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220263101729 / 10000000000000 : ℝ))
      (E := (cell13120 ⟨44, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (10319719312253 / 12500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (220263101729 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_45 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82523925647939 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202635060219 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨45, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82523925647939 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202635060219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_46 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (20622530045377 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202639065279 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨46, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (20622530045377 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202639065279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_47 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41228169034917 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101321544639 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨47, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41228169034917 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101321544639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_48 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82422579284161 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101323564967 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨48, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82422579284161 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101323564967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_49 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (2059721094897 / 2500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (275331390719 / 12500000000000 : ℝ))
      (E := (cell13120 ⟨49, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (2059721094897 / 2500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (275331390719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_50 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (20588782894131 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101327566487 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨50, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (20588782894131 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101327566487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_51 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (10290180324721 / 12500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202659148681 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨51, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (10290180324721 / 12500000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202659148681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_52 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (8228777683143 / 10000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202663169743 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨52, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (8228777683143 / 10000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202663169743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_53 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41127067124733 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101333596411 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨53, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41127067124733 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101333596411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_54 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (3288820592959 / 4000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202671214367 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨54, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (3288820592959 / 4000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202671214367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_55 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (82186918527193 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101337615311 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨55, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (82186918527193 / 100000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101337615311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_56 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (41076672665747 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (275334904703 / 12500000000000 : ℝ))
      (E := (cell13120 ⟨56, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (41076672665747 / 50000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (275334904703 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_57 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (5132487200587 / 6250000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (550670822597 / 25000000000000 : ℝ))
      (E := (cell13120 ⟨57, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (5132487200587 / 6250000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (550670822597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_58 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (16417253626707 / 20000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202687266187 / 100000000000000 : ℝ))
      (E := (cell13120 ⟨58, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (16417253626707 / 20000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (2202687266187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13120_59 : CellCertificate 13120 (875317699011949 / 10000000000000000 : ℝ) (1600930459248681 / 1000000000000000000 : ℝ) (323135460851973 / 10000000000000000 : ℝ)
    (cell13120 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · norm_num [cell13120]
  · have h := gap_lower (n := 13120) (a := (20513191019177 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101345639419 / 50000000000000 : ℝ))
      (E := (cell13120 ⟨59, by decide⟩).energy) (xi := (323135460851973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13120 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13120) (a := (20513191019177 / 25000000000000 : ℝ)) (b := (19617127083 / 12500000000000 : ℝ)) (q := (1101345639419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13120]

theorem cert13121_40 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41346645195787 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101251688127 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨40, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41346645195787 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101251688127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_41 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41329683860517 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202507375143 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨41, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41329683860517 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202507375143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_42 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (20656367137801 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (68828481291 / 3125000000000 : ℝ))
      (E := (cell13121 ⟨42, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (20656367137801 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (68828481291 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_43 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41295796426299 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202515453553 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨43, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41295796426299 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202515453553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_44 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41278870297939 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101259735779 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨44, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41278870297939 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101259735779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_45 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (20630977937963 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202523453619 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨45, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (20630977937963 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202523453619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_46 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (20622526572869 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (68828983023 / 3125000000000 : ℝ))
      (E := (cell13121 ⟨46, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (20622526572869 / 25000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (68828983023 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_47 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82456324185851 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202531478839 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨47, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82456324185851 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202531478839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_48 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82422565406223 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550633879411 / 25000000000000 : ℝ))
      (E := (cell13121 ⟨48, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82422565406223 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550633879411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_49 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82388829923981 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101269755829 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨49, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82388829923981 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101269755829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_50 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (4117755885533 / 5000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (137658973509 / 6250000000000 : ℝ))
      (E := (cell13121 ⟨50, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (4117755885533 / 5000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (137658973509 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_51 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41160714368967 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202547590163 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨51, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41160714368967 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202547590163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_52 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82287762977621 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101275804791 / 50000000000000 : ℝ))
      (E := (cell13121 ⟨52, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82287762977621 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (1101275804791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_53 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41127060200839 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202555571971 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨53, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41127060200839 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202555571971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_54 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41110250491101 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202559591943 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨54, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41110250491101 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202559591943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_55 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82186904691431 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202563606669 / 100000000000000 : ℝ))
      (E := (cell13121 ⟨55, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82186904691431 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (2202563606669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_56 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41076665750869 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (275320958919 / 12500000000000 : ℝ))
      (E := (cell13121 ⟨56, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41076665750869 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (275320958919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_57 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82119781385637 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550642915879 / 25000000000000 : ℝ))
      (E := (cell13121 ⟨57, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82119781385637 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (550642915879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_58 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (82086254315777 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (440515139427 / 20000000000000 : ℝ))
      (E := (cell13121 ⟨58, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (82086254315777 / 100000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (440515139427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13121_59 : CellCertificate 13121 (175058290723361 / 2000000000000000 : ℝ) (800404203789973 / 500000000000000000 : ℝ) (323110269192213 / 10000000000000000 : ℝ)
    (cell13121 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · norm_num [cell13121]
  · have h := gap_lower (n := 13121) (a := (41026375132471 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (137661231779 / 6250000000000 : ℝ))
      (E := (cell13121 ⟨59, by decide⟩).energy) (xi := (323110269192213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13121 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13121) (a := (41026375132471 / 50000000000000 : ℝ)) (b := (78462459439 / 50000000000000 : ℝ)) (q := (137661231779 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13121]

theorem cert13122_40 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82693276467267 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101195917311 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨40, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82693276467267 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101195917311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_41 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (16531870760561 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202395831363 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨41, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (16531870760561 / 20000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202395831363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_42 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (10328181829881 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (220239985543 / 10000000000000 : ℝ))
      (E := (cell13122 ⟨42, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (10328181829881 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (220239985543 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_43 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82591578946511 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550600961689 / 25000000000000 : ℝ))
      (E := (cell13122 ⟨43, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82591578946511 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550600961689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_44 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41278863347927 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (275300982841 / 12500000000000 : ℝ))
      (E := (cell13122 ⟨44, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41278863347927 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (275300982841 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_45 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41261948928943 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101205950853 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨45, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41261948928943 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101205950853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_46 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82490092403563 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440483180581 / 20000000000000 : ℝ))
      (E := (cell13122 ⟨46, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82490092403563 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (440483180581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_47 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82456310303987 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (34412811299 / 1562500000000 : ℝ))
      (E := (cell13122 ⟨47, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82456310303987 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (34412811299 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_48 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41211275765201 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550605990029 / 25000000000000 : ℝ))
      (E := (cell13122 ⟨48, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41211275765201 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550605990029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_49 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (411944080271 / 500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202427952349 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨49, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (411944080271 / 500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202427952349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_50 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (160849812201 / 195312500000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (27530399451 / 1250000000000 : ℝ))
      (E := (cell13122 ⟨50, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (160849812201 / 195312500000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (27530399451 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_51 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (10290176860027 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202435968387 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨51, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (10290176860027 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202435968387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_52 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82287749125927 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202439986141 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨52, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82287749125927 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202439986141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_53 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82254106556003 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550611001501 / 25000000000000 : ℝ))
      (E := (cell13122 ⟨53, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82254106556003 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (550611001501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_54 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (41110243571271 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (275306003053 / 12500000000000 : ℝ))
      (E := (cell13122 ⟨54, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (41110243571271 / 50000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (275306003053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_55 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (4109344542889 / 5000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (137653252353 / 6250000000000 : ℝ))
      (E := (cell13122 ⟨55, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (4109344542889 / 5000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (137653252353 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_56 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82153317674093 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (275307012609 / 12500000000000 : ℝ))
      (E := (cell13122 ⟨56, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82153317674093 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (275307012609 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_57 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (10264970945499 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (17619680733 / 800000000000 : ℝ))
      (E := (cell13122 ⟨57, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (10264970945499 / 12500000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (17619680733 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_58 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82086240500127 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202464123877 / 100000000000000 : ℝ))
      (E := (cell13122 ⟨58, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82086240500127 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (2202464123877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13122_59 : CellCertificate 13122 (875265212050213 / 10000000000000000 : ℝ) (160068637451973 / 100000000000000000 : ℝ) (323085081487579 / 10000000000000000 : ℝ)
    (cell13122 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · norm_num [cell13122]
  · have h := gap_lower (n := 13122) (a := (82052736455283 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101234066943 / 50000000000000 : ℝ))
      (E := (cell13122 ⟨59, by decide⟩).energy) (xi := (323085081487579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13122 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13122) (a := (82052736455283 / 100000000000000 : ℝ)) (b := (31382564593 / 20000000000000 : ℝ)) (q := (1101234066943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13122]

theorem cert13123_40 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (16538652509017 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440456045997 / 20000000000000 : ℝ))
      (E := (cell13123 ⟨40, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (16538652509017 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440456045997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_41 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (826593398867 / 1000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440456856673 / 20000000000000 : ℝ))
      (E := (cell13123 ⟨41, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (826593398867 / 1000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440456856673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_42 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (10328180091127 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220228830533 / 10000000000000 : ℝ))
      (E := (cell13123 ⟨42, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (10328180091127 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220228830533 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_43 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (16518313008509 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101146147301 / 50000000000000 : ℝ))
      (E := (cell13123 ⟨43, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (16518313008509 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (1101146147301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_44 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82557712797951 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550574077141 / 25000000000000 : ℝ))
      (E := (cell13123 ⟨44, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82557712797951 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550574077141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_45 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (2063097099151 / 2500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202300345579 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨45, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (2063097099151 / 2500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202300345579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_46 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (8249007851777 / 10000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202304344861 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨46, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (8249007851777 / 10000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202304344861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_47 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82456296424241 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202308363221 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨47, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82456296424241 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202308363221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_48 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82422537656699 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (275289049797 / 12500000000000 : ℝ))
      (E := (cell13123 ⟨48, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82422537656699 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (275289049797 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_49 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (16477760437307 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220231638883 / 10000000000000 : ℝ))
      (E := (cell13123 ⟨49, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (16477760437307 / 20000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220231638883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_50 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (64339914051 / 78125000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550580097707 / 25000000000000 : ℝ))
      (E := (cell13123 ⟨50, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (64339914051 / 78125000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (550580097707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_51 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (20580350256153 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (275290550181 / 12500000000000 : ℝ))
      (E := (cell13123 ⟨51, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (20580350256153 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (275290550181 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_52 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41143867638173 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220232847663 / 10000000000000 : ℝ))
      (E := (cell13123 ⟨52, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41143867638173 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (220232847663 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_53 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82254092712441 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202332494921 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨53, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82254092712441 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202332494921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_54 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82220473304993 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202336511817 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨54, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82220473304993 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202336511817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_55 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (82186877026241 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (55058513089 / 2500000000000 : ℝ))
      (E := (cell13123 ⟨55, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (82186877026241 / 100000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (55058513089 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_56 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41076651924279 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202344526187 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨56, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41076651924279 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202344526187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_57 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (10264969218057 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202348515529 / 100000000000000 : ℝ))
      (E := (cell13123 ⟨57, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (10264969218057 / 12500000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (2202348515529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_58 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (41043113343293 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (137647034151 / 6250000000000 : ℝ))
      (E := (cell13123 ⟨58, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (41043113343293 / 50000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (137647034151 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13123_59 : CellCertificate 13123 (437619487155647 / 5000000000000000 : ℝ) (1600564360063779 / 1000000000000000000 : ℝ) (323059897737089 / 10000000000000000 : ℝ)
    (cell13123 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · norm_num [cell13123]
  · have h := gap_lower (n := 13123) (a := (20513180661933 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440471311021 / 20000000000000 : ℝ))
      (E := (cell13123 ⟨59, by decide⟩).energy) (xi := (323059897737089 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13123 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13123) (a := (20513180661933 / 25000000000000 : ℝ)) (b := (156900728923 / 100000000000000 : ℝ)) (q := (440471311021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13123]

theorem cert13124_40 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82693248625027 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (440433747741 / 20000000000000 : ℝ))
      (E := (cell13124 ⟨40, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82693248625027 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (440433747741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_41 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (41329662986359 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202172731151 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨41, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (41329662986359 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202172731151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_42 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (16525085364221 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (275272093877 / 12500000000000 : ℝ))
      (E := (cell13124 ⟨42, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (16525085364221 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (275272093877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_43 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82591551140701 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (275272592279 / 12500000000000 : ℝ))
      (E := (cell13124 ⟨43, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82591551140701 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (275272592279 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_44 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (10319712362771 / 12500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101092375093 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨44, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (10319712362771 / 12500000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101092375093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_45 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (41261935038157 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101094392619 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨45, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (41261935038157 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101094392619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_46 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (5155629039631 / 6250000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202192782603 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨46, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (5155629039631 / 6250000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202192782603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_47 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82456282546613 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101098399547 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨47, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82456282546613 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101098399547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_48 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82422523785113 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (275275104053 / 12500000000000 : ℝ))
      (E := (cell13124 ⟨48, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82422523785113 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (275275104053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_49 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (16477757664197 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (22022048801 / 1000000000000 : ℝ))
      (E := (cell13124 ⟨49, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (16477757664197 / 20000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (22022048801 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_50 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82355076125763 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (550552220097 / 25000000000000 : ℝ))
      (E := (cell13124 ⟨50, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82355076125763 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (550552220097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_51 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (41160693585561 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (440442577869 / 20000000000000 : ℝ))
      (E := (cell13124 ⟨51, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (41160693585561 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (440442577869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_52 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (41143860714439 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202216903843 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨52, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (41143860714439 / 50000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202216903843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_53 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82254078870991 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202220920539 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨53, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82254078870991 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202220920539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_54 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20555114867389 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202224935887 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨54, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20555114867389 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202224935887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_55 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20546715799203 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202228946127 / 100000000000000 : ℝ))
      (E := (cell13124 ⟨55, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20546715799203 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (2202228946127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_56 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (20538322506283 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101116503231 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨56, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (20538322506283 / 25000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101116503231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_57 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82119739927029 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (137639812151 / 6250000000000 : ℝ))
      (E := (cell13124 ⟨57, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82119739927029 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (137639812151 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_58 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (82086212875153 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101120511981 / 50000000000000 : ℝ))
      (E := (cell13124 ⟨58, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (82086212875153 / 100000000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (1101120511981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

theorem cert13124_59 : CellCertificate 13124 (875212740399169 / 10000000000000000 : ℝ) (800221182103919 / 500000000000000000 : ℝ) (323034717939759 / 10000000000000000 : ℝ)
    (cell13124 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · norm_num [cell13124]
  · have h := gap_lower (n := 13124) (a := (5128294302643 / 6250000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (550561257839 / 25000000000000 : ℝ))
      (E := (cell13124 ⟨59, by decide⟩).energy) (xi := (323034717939759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13124 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13124) (a := (5128294302643 / 6250000000000 : ℝ)) (b := (9805539797 / 6250000000000 : ℝ)) (q := (550561257839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13124]

end BstLean.Part268
