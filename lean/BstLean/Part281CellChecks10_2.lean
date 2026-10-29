import BstLean.Part281CellChecks10_1

namespace BstLean.Part281
open Real BstLean.Part263

theorem cert12109_40 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82697835360899 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (116663644037 / 5000000000000 : ℝ))
      (E := (cell12109 ⟨40, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82697835360899 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (116663644037 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_41 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82663645501077 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (583319218239 / 25000000000000 : ℝ))
      (E := (cell12109 ⟨41, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82663645501077 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (583319218239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_42 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82629479510657 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333280856377 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨42, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82629479510657 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333280856377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_43 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (2064883433987 / 2500000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (291660603893 / 12500000000000 : ℝ))
      (E := (cell12109 ⟨43, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (2064883433987 / 2500000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (291660603893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_44 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (4128060950877 / 5000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (1166644398587 / 50000000000000 : ℝ))
      (E := (cell12109 ⟨44, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (4128060950877 / 5000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (1166644398587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_45 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (41263562227491 / 50000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (233329281297 / 10000000000000 : ℝ))
      (E := (cell12109 ⟨45, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (41263562227491 / 50000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (233329281297 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_46 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82493053642103 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333296819253 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨46, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82493053642103 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333296819253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_47 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82459006549349 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333300815287 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨47, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82459006549349 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333300815287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_48 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (20606245786829 / 25000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (145831550007 / 6250000000000 : ℝ))
      (E := (cell12109 ⟨48, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (20606245786829 / 25000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (145831550007 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_49 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (329563933627 / 400000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (466661754511 / 20000000000000 : ℝ))
      (E := (cell12109 ⟨49, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (329563933627 / 400000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (466661754511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_50 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82357007298541 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333312790147 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨50, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82357007298541 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333312790147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_51 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (80393608197 / 97656250000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (233331679241 / 10000000000000 : ℝ))
      (E := (cell12109 ⟨51, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (80393608197 / 97656250000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (233331679241 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_52 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (16457825172699 / 20000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333320777523 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨52, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (16457825172699 / 20000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333320777523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_53 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82255220479173 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333324743451 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨53, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82255220479173 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333324743451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_54 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82221338612233 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (1166664373483 / 50000000000000 : ℝ))
      (E := (cell12109 ⟨54, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82221338612233 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (1166664373483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_55 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (82187480234293 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (29166659083 / 1250000000000 : ℝ))
      (E := (cell12109 ⟨55, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (82187480234293 / 100000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (29166659083 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_56 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (10269205664639 / 12500000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (1166668369433 / 50000000000000 : ℝ))
      (E := (cell12109 ⟨56, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (10269205664639 / 12500000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (1166668369433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_57 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (8211983383259 / 10000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333340721749 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨57, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (8211983383259 / 10000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333340721749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_58 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (1282594464887 / 1562500000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333344731309 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨58, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (1282594464887 / 1562500000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333344731309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12109_59 : CellCertificate 12109 (451987577668613 / 5000000000000000 : ℝ) (173464082635433 / 100000000000000000 : ℝ) (21951216159441 / 625000000000000 : ℝ)
    (cell12109 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · norm_num [cell12109]
  · have h := gap_lower (n := 12109) (a := (8205228104983 / 10000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333348705183 / 100000000000000 : ℝ))
      (E := (cell12109 ⟨59, by decide⟩).energy) (xi := (21951216159441 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12109 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12109]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12109])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12109) (a := (8205228104983 / 10000000000000 : ℝ)) (b := (170308037669 / 100000000000000 : ℝ)) (q := (2333348705183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12109])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12109]

theorem cert12110_40 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (82697832126669 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333110780041 / 100000000000000 : ℝ))
      (E := (cell12110 ⟨40, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (82697832126669 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333110780041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_41 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (82663642592547 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (93324589069 / 4000000000000 : ℝ))
      (E := (cell12110 ⟨41, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (82663642592547 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (93324589069 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_42 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (5164342307961 / 6250000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (291639840509 / 12500000000000 : ℝ))
      (E := (cell12110 ⟨42, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (5164342307961 / 6250000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (291639840509 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_43 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (20648833775249 / 25000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333122713539 / 100000000000000 : ℝ))
      (E := (cell12110 ⟨43, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (20648833775249 / 25000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333122713539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_44 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (82561217083403 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (1166563347521 / 50000000000000 : ℝ))
      (E := (cell12110 ⟨44, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (82561217083403 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (1166563347521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_45 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (41263561422371 / 50000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333130727083 / 100000000000000 : ℝ))
      (E := (cell12110 ⟨45, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (41263561422371 / 50000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333130727083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_46 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (5155815772207 / 6250000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (583283672889 / 25000000000000 : ℝ))
      (E := (cell12110 ⟨46, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (5155815772207 / 6250000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (583283672889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_47 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (2061475139639 / 2500000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333138705351 / 100000000000000 : ℝ))
      (E := (cell12110 ⟨47, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (2061475139639 / 2500000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333138705351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_48 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (82424982506083 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333142708707 / 100000000000000 : ℝ))
      (E := (cell12110 ⟨48, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (82424982506083 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333142708707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_49 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (659127864701 / 800000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (46662934009 / 2000000000000 : ℝ))
      (E := (cell12110 ⟨49, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (659127864701 / 800000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (46662934009 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_50 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (82357007301079 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (233315067919 / 10000000000000 : ℝ))
      (E := (cell12110 ⟨50, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (82357007301079 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (233315067919 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_51 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (16464611023497 / 20000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (58328866083 / 2500000000000 : ℝ))
      (E := (cell12110 ⟨51, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (16464611023497 / 20000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (58328866083 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_52 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (20572281627007 / 25000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333158649987 / 100000000000000 : ℝ))
      (E := (cell12110 ⟨52, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (20572281627007 / 25000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333158649987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_53 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (41127610722019 / 50000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466632527647 / 20000000000000 : ℝ))
      (E := (cell12110 ⟨53, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (41127610722019 / 50000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466632527647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_54 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (20555334974247 / 25000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466633332967 / 20000000000000 : ℝ))
      (E := (cell12110 ⟨54, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (20555334974247 / 25000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466633332967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_55 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (82187481838497 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (58329265233 / 2500000000000 : ℝ))
      (E := (cell12110 ⟨55, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (82187481838497 / 100000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (58329265233 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_56 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (20538411810081 / 25000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466634929227 / 20000000000000 : ℝ))
      (E := (cell12110 ⟨56, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (20538411810081 / 25000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466634929227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_57 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (8211983607437 / 10000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466635719057 / 20000000000000 : ℝ))
      (E := (cell12110 ⟨57, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (8211983607437 / 10000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466635719057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_58 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (41043024156339 / 50000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466636526187 / 20000000000000 : ℝ))
      (E := (cell12110 ⟨58, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (41043024156339 / 50000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (466636526187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12110_59 : CellCertificate 12110 (180788907460463 / 2000000000000000 : ℝ) (216812192074839 / 125000000000000000 : ℝ) (351189728893689 / 10000000000000000 : ℝ)
    (cell12110 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · norm_num [cell12110]
  · have h := gap_lower (n := 12110) (a := (8205228392743 / 10000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333186631661 / 100000000000000 : ℝ))
      (E := (cell12110 ⟨59, by decide⟩).energy) (xi := (351189728893689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12110 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12110]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12110])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12110) (a := (8205228392743 / 10000000000000 : ℝ)) (b := (170293797929 / 100000000000000 : ℝ)) (q := (2333186631661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12110])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12110]

theorem cert12111_40 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (82697828893483 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (583237198217 / 25000000000000 : ℝ))
      (E := (cell12111 ⟨40, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (82697828893483 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (583237198217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_41 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (82663639685019 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166476376409 / 50000000000000 : ℝ))
      (E := (cell12111 ⟨41, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (82663639685019 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166476376409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_42 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (41314737172527 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2332956764207 / 100000000000000 : ℝ))
      (E := (cell12111 ⟨42, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (41314737172527 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2332956764207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_43 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (8259533284343 / 10000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2332960768487 / 100000000000000 : ℝ))
      (E := (cell12111 ⟨43, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (8259533284343 / 10000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2332960768487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_44 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (82561215150143 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (93318590623 / 4000000000000 : ℝ))
      (E := (cell12111 ⟨44, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (82561215150143 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (93318590623 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_45 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (82527121235339 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (233296875517 / 10000000000000 : ℝ))
      (E := (cell12111 ⟨45, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (82527121235339 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (233296875517 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_46 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (41246525534659 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2332972736747 / 100000000000000 : ℝ))
      (E := (cell12111 ⟨46, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (41246525534659 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2332972736747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_47 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (41229502311263 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (36452761087 / 1562500000000 : ℝ))
      (E := (cell12111 ⟨47, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (41229502311263 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (36452761087 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_48 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (41212490932781 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166490365773 / 50000000000000 : ℝ))
      (E := (cell12111 ⟨48, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (41212490932781 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166490365773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_49 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (20597745692293 / 25000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2332984683781 / 100000000000000 : ℝ))
      (E := (cell12111 ⟨49, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (20597745692293 / 25000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2332984683781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_50 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (82357007304249 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166494341327 / 50000000000000 : ℝ))
      (E := (cell12111 ⟨50, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (82357007304249 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166494341327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_51 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (41161527720917 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (583248166921 / 25000000000000 : ℝ))
      (E := (cell12111 ⟨51, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (41161527720917 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (583248166921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_52 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (82289127153111 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166498348009 / 50000000000000 : ℝ))
      (E := (cell12111 ⟨52, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (82289127153111 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166498348009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_53 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (20563805602353 / 25000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2333000647709 / 100000000000000 : ℝ))
      (E := (cell12111 ⟨53, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (20563805602353 / 25000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2333000647709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_54 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (20555335295553 / 25000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (583251159617 / 25000000000000 : ℝ))
      (E := (cell12111 ⟨54, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (20555335295553 / 25000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (583251159617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_55 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (82187483443129 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166504332953 / 50000000000000 : ℝ))
      (E := (cell12111 ⟨55, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (82187483443129 / 100000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (1166504332953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_56 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (20538412290981 / 25000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (58325316709 / 2500000000000 : ℝ))
      (E := (cell12111 ⟨56, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (20538412290981 / 25000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (58325316709 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_57 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (41059919158249 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (46660332859 / 2000000000000 : ℝ))
      (E := (cell12111 ⟨57, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (41059919158249 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (46660332859 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_58 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (41043025436447 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (466604129139 / 20000000000000 : ℝ))
      (E := (cell12111 ⟨58, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (41043025436447 / 50000000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (466604129139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12111_59 : CellCertificate 12111 (451956962072663 / 5000000000000000 : ℝ) (346870854102799 / 200000000000000000 : ℝ) (351160004426947 / 10000000000000000 : ℝ)
    (cell12111 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · norm_num [cell12111]
  · have h := gap_lower (n := 12111) (a := (5128267925331 / 6250000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2333024614229 / 100000000000000 : ℝ))
      (E := (cell12111 ⟨59, by decide⟩).energy) (xi := (351160004426947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12111 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12111]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12111])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12111) (a := (5128267925331 / 6250000000000 : ℝ)) (b := (17027956061 / 10000000000000 : ℝ)) (q := (2333024614229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12111])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12111]

theorem cert12112_40 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (4134891283067 / 5000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (1166393459613 / 50000000000000 : ℝ))
      (E := (cell12112 ⟨40, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (4134891283067 / 5000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (1166393459613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_41 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82663636778493 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (58319773781 / 2500000000000 : ℝ))
      (E := (cell12112 ⟨41, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82663636778493 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (58319773781 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_42 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82629471763693 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (46655898361 / 2000000000000 : ℝ))
      (E := (cell12112 ⟨42, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82629471763693 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (46655898361 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_43 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (2581104080837 / 3125000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (1166399439239 / 50000000000000 : ℝ))
      (E := (cell12112 ⟨43, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (2581104080837 / 3125000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (1166399439239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_44 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82561213217761 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332802891219 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨44, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82561213217761 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332802891219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_45 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82527119626773 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (583201724309 / 25000000000000 : ℝ))
      (E := (cell12112 ⟨45, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82527119626773 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (583201724309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_46 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (41246524892059 / 50000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332810896009 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨46, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (41246524892059 / 50000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332810896009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_47 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (41229501830123 / 50000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332814886793 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨47, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (41229501830123 / 50000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332814886793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_48 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (16484996245151 / 20000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332818868631 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨48, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (16484996245151 / 20000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332818868631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_49 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (1287359100803 / 1562500000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (466564568069 / 20000000000000 : ℝ))
      (E := (cell12112 ⟨49, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (1287359100803 / 1562500000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (466564568069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_50 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82357007308051 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (291603357433 / 12500000000000 : ℝ))
      (E := (cell12112 ⟨50, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82357007308051 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (291603357433 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_51 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82323055766773 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332830865507 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨51, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82323055766773 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332830865507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_52 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (10286140974843 / 12500000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332834856653 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨52, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (10286140974843 / 12500000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332834856653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_53 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (1285237865239 / 1562500000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (1166419415433 / 50000000000000 : ℝ))
      (E := (cell12112 ⟨53, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (1285237865239 / 1562500000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (1166419415433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_54 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (16444268493581 / 20000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332842844911 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨54, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (16444268493581 / 20000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332842844911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_55 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (8218748504819 / 10000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332846837361 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨55, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (8218748504819 / 10000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332846837361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_56 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82153651087911 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (466570161109 / 20000000000000 : ℝ))
      (E := (cell12112 ⟨56, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82153651087911 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (466570161109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_57 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (20529960139743 / 25000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (466570961133 / 20000000000000 : ℝ))
      (E := (cell12112 ⟨57, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (20529960139743 / 25000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (466570961133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_58 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82086053433417 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332858775591 / 100000000000000 : ℝ))
      (E := (cell12112 ⟨58, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82086053433417 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (2332858775591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12112_59 : CellCertificate 12112 (903883315865039 / 10000000000000000 : ℝ) (346842205618863 / 200000000000000000 : ℝ) (17556514257463 / 500000000000000 : ℝ)
    (cell12112 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · norm_num [cell12112]
  · have h := gap_lower (n := 12112) (a := (82052289683429 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (466572554231 / 20000000000000 : ℝ))
      (E := (cell12112 ⟨59, by decide⟩).energy) (xi := (17556514257463 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12112 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12112]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12112])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12112) (a := (82052289683429 / 100000000000000 : ℝ)) (b := (170265325709 / 100000000000000 : ℝ)) (q := (466572554231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12112])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12112]

theorem cert12113_40 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (82697822430239 / 100000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332625217801 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨40, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (82697822430239 / 100000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332625217801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_41 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (82663633872967 / 100000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332629204577 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨41, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (82663633872967 / 100000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332629204577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_42 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (20657367295823 / 25000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (466526637121 / 20000000000000 : ℝ))
      (E := (cell12113 ⟨42, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (20657367295823 / 25000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (466526637121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_43 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (16519065666211 / 20000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332637161027 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨43, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (16519065666211 / 20000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332637161027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_44 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (5160075705391 / 6250000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (583160297383 / 25000000000000 : ℝ))
      (E := (cell12113 ⟨44, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (5160075705391 / 6250000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (583160297383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_45 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41263559009521 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (583161288321 / 25000000000000 : ℝ))
      (E := (cell12113 ⟨45, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41263559009521 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (583161288321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_46 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41246524249857 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332649169339 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨46, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41246524249857 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332649169339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_47 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (515368766867 / 625000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332653178177 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨47, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (515368766867 / 625000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332653178177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_48 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (82424980586661 / 100000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (583164279991 / 25000000000000 : ℝ))
      (E := (cell12113 ⟨48, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (82424980586661 / 100000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (583164279991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_49 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (20597745533571 / 25000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (1166330555623 / 50000000000000 : ℝ))
      (E := (cell12113 ⟨49, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (20597745533571 / 25000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (1166330555623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_50 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (20589251828121 / 25000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332665150701 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨50, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (20589251828121 / 25000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332665150701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_51 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41161528046151 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332669118903 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨51, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41161528046151 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332669118903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_52 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41144564222463 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (1166336565947 / 50000000000000 : ℝ))
      (E := (cell12113 ⟨52, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41144564222463 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (1166336565947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_53 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (82255224341689 / 100000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332677128717 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨53, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (82255224341689 / 100000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332677128717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_54 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41110671877033 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332681107123 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨54, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41110671877033 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332681107123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_55 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41093743326839 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332685064651 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨55, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41093743326839 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332685064651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_56 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41076826506143 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (233268905769 / 10000000000000 : ℝ))
      (E := (cell12113 ⟨56, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41076826506143 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (233268905769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_57 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41059921400897 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332693083429 / 100000000000000 : ℝ))
      (E := (cell12113 ⟨57, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41059921400897 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (2332693083429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_58 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (41043027997123 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (291587134967 / 12500000000000 : ℝ))
      (E := (cell12113 ⟨58, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (41043027997123 / 50000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (291587134967 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12113_59 : CellCertificate 12113 (180770542492047 / 2000000000000000 : ℝ) (108379238083363 / 62500000000000000 : ℝ) (175550285529529 / 5000000000000000 : ℝ)
    (cell12113 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · norm_num [cell12113]
  · have h := gap_lower (n := 12113) (a := (20513073140457 / 25000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (583175260827 / 25000000000000 : ℝ))
      (E := (cell12113 ⟨59, by decide⟩).energy) (xi := (175550285529529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12113 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12113]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12113])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12113) (a := (20513073140457 / 25000000000000 : ℝ)) (b := (85125546613 / 50000000000000 : ℝ)) (q := (583175260827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12113])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12113]

theorem cert12114_40 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (4134890960009 / 5000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332463629909 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨40, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (4134890960009 / 5000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332463629909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_41 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (82663630968443 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332467630243 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨41, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (82663630968443 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332467630243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_42 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (82629466603849 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332471625607 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨42, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (82629466603849 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332471625607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_43 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (16519065215249 / 20000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (583118904033 / 25000000000000 : ℝ))
      (E := (cell12114 ⟨43, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (16519065215249 / 20000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (583118904033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_44 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (20640302338907 / 25000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332479601737 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨44, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (20640302338907 / 25000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332479601737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_45 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (82527116412147 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (466496716423 / 20000000000000 : ℝ))
      (E := (cell12114 ⟨45, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (82527116412147 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (466496716423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_46 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (10311630902013 / 12500000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (116624377837 / 5000000000000 : ℝ))
      (E := (cell12114 ⟨46, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (10311630902013 / 12500000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (116624377837 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_47 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (20614750434487 / 25000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332491583721 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨47, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (20614750434487 / 25000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332491583721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_48 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (2060624498707 / 2500000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (116624777221 / 5000000000000 : ℝ))
      (E := (cell12114 ⟨48, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (2060624498707 / 2500000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (116624777221 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_49 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (10298872727231 / 12500000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332499555383 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨49, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (10298872727231 / 12500000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332499555383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_50 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (82357007317547 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (1166251778183 / 50000000000000 : ℝ))
      (E := (cell12114 ⟨50, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (82357007317547 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (1166251778183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_51 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (41161528209211 / 50000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332507545759 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨51, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (41161528209211 / 50000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332507545759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_52 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (41144564545829 / 50000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332511521741 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨52, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (41144564545829 / 50000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332511521741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_53 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (8225522530859 / 10000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (145782221329 / 6250000000000 : ℝ))
      (E := (cell12114 ⟨53, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (8225522530859 / 10000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (145782221329 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_54 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (16444269008139 / 20000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332519484119 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨54, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (16444269008139 / 20000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332519484119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_55 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (82187488259593 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332523524891 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨55, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (82187488259593 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332523524891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_56 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (82153654937047 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (116626374193 / 5000000000000 : ℝ))
      (E := (cell12114 ⟨56, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (82153654937047 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (116626374193 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_57 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (41059922522481 / 50000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332531476243 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨57, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (41059922522481 / 50000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332531476243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_58 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (41043029277691 / 50000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332535499019 / 100000000000000 : ℝ))
      (E := (cell12114 ⟨58, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (41043029277691 / 50000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (2332535499019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12114_59 : CellCertificate 12114 (225955528482423 / 2500000000000000 : ℝ) (1733924614226613 / 1000000000000000000 : ℝ) (35107086215477 / 1000000000000000 : ℝ)
    (cell12114 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · norm_num [cell12114]
  · have h := gap_lower (n := 12114) (a := (82052295440493 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (1166269744911 / 50000000000000 : ℝ))
      (E := (cell12114 ⟨59, by decide⟩).energy) (xi := (35107086215477 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12114 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12114]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12114])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12114) (a := (82052295440493 / 100000000000000 : ℝ)) (b := (170236863161 / 100000000000000 : ℝ)) (q := (1166269744911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12114])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12114]

theorem cert12115_40 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82697815971163 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166151077777 / 50000000000000 : ℝ))
      (E := (cell12115 ⟨40, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82697815971163 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166151077777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_41 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (41331814032459 / 50000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166153084769 / 50000000000000 : ℝ))
      (E := (cell12115 ⟨41, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (41331814032459 / 50000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166153084769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_42 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82629464025367 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332310120589 / 100000000000000 : ℝ))
      (E := (cell12115 ⟨42, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82629464025367 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332310120589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_43 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82595323822353 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (145769632893 / 6250000000000 : ℝ))
      (E := (cell12115 ⟨43, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82595323822353 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (145769632893 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_44 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82561207425877 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (583079531959 / 25000000000000 : ℝ))
      (E := (cell12115 ⟨44, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82561207425877 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (583079531959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_45 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (10315889350761 / 12500000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (233232212493 / 10000000000000 : ℝ))
      (E := (cell12115 ⟨45, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (10315889350761 / 12500000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (233232212493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_46 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (10311630741661 / 12500000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166163058521 / 50000000000000 : ℝ))
      (E := (cell12115 ⟨46, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (10311630741661 / 12500000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166163058521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_47 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82459000777929 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332330103429 / 100000000000000 : ℝ))
      (E := (cell12115 ⟨47, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82459000777929 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332330103429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_48 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82424979310611 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332334083129 / 100000000000000 : ℝ))
      (E := (cell12115 ⟨48, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82424979310611 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332334083129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_49 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82390981502083 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (466467610993 / 20000000000000 : ℝ))
      (E := (cell12115 ⟨49, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82390981502083 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (466467610993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_50 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (41178503661621 / 50000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332342076461 / 100000000000000 : ℝ))
      (E := (cell12115 ⟨50, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (41178503661621 / 50000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332342076461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_51 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82323056745131 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (72885815223 / 3125000000000 : ℝ))
      (E := (cell12115 ⟨51, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82323056745131 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (72885815223 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_52 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82289129738939 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (583087521291 / 25000000000000 : ℝ))
      (E := (cell12115 ⟨52, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82289129738939 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (583087521291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_53 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (20563806569 / 25000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (583088517127 / 25000000000000 : ℝ))
      (E := (cell12115 ⟨53, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (20563806569 / 25000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (583088517127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_54 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (5138834145487 / 6250000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332358034917 / 100000000000000 : ℝ))
      (E := (cell12115 ⟨54, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (5138834145487 / 6250000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332358034917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_55 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (5136718116621 / 6250000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (291545255121 / 12500000000000 : ℝ))
      (E := (cell12115 ⟨55, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (5136718116621 / 6250000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (291545255121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_56 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (20538414215549 / 25000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332366024993 / 100000000000000 : ℝ))
      (E := (cell12115 ⟨56, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (20538414215549 / 25000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (2332366024993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_57 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (20529961822119 / 25000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166185021599 / 50000000000000 : ℝ))
      (E := (cell12115 ⟨57, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (20529961822119 / 25000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166185021599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_58 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82086061116823 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166187016723 / 50000000000000 : ℝ))
      (E := (cell12115 ⟨58, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82086061116823 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (1166187016723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12115_59 : CellCertificate 12115 (903791520272193 / 10000000000000000 : ℝ) (216722680345859 / 125000000000000000 : ℝ) (87760289608707 / 2500000000000000 : ℝ)
    (cell12115 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · norm_num [cell12115]
  · have h := gap_lower (n := 12115) (a := (82052298319423 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (466475598487 / 20000000000000 : ℝ))
      (E := (cell12115 ⟨59, by decide⟩).energy) (xi := (87760289608707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12115 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12115]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12115])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12115) (a := (82052298319423 / 100000000000000 : ℝ)) (b := (21277829439 / 12500000000000 : ℝ)) (q := (466475598487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12115])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12115]

theorem cert12116_40 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82697812743187 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (466428158947 / 20000000000000 : ℝ))
      (E := (cell12116 ⟨40, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82697812743187 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (466428158947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_41 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (41331812581197 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332144822457 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨41, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (41331812581197 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332144822457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_42 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (41314730723921 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (1166074394011 / 50000000000000 : ℝ))
      (E := (cell12116 ⟨42, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (41314730723921 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (1166074394011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_43 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82595321569379 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (583038202251 / 25000000000000 : ℝ))
      (E := (cell12116 ⟨43, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82595321569379 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (583038202251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_44 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (41280602748501 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332156767831 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨44, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (41280602748501 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332156767831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_45 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (2578972287527 / 3125000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332160781729 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨45, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (2578972287527 / 3125000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332160781729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_46 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82493044651267 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332164791417 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨46, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82493044651267 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332164791417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_47 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82458999818663 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332168737299 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨47, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82458999818663 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332168737299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_48 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (41212489336827 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332172736091 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨48, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (41212489336827 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332172736091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_49 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82390981186989 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (1166088363893 / 50000000000000 : ℝ))
      (E := (cell12116 ⟨49, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82390981186989 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (1166088363893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_50 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82357007329567 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (583045177747 / 25000000000000 : ℝ))
      (E := (cell12116 ⟨50, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82357007329567 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (583045177747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_51 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (8232305707243 / 10000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (291523092879 / 12500000000000 : ℝ))
      (E := (cell12116 ⟨51, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (8232305707243 / 10000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (291523092879 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_52 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82289130386769 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332188704229 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨52, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82289130386769 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332188704229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_53 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82255227243919 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (46643854209 / 2000000000000 : ℝ))
      (E := (cell12116 ⟨53, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82255227243919 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (46643854209 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_54 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82221347615357 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (1166098350251 / 50000000000000 : ℝ))
      (E := (cell12116 ⟨54, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82221347615357 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (1166098350251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_55 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (41093745736353 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (29152508399 / 1250000000000 : ℝ))
      (E := (cell12116 ⟨55, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (41093745736353 / 50000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (29152508399 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_56 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82153658787731 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (583051170273 / 25000000000000 : ℝ))
      (E := (cell12116 ⟨56, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82153658787731 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (583051170273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_57 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82119849532337 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332208666119 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨57, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82119849532337 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332208666119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_58 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (82086063678571 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332212683013 / 100000000000000 : ℝ))
      (E := (cell12116 ⟨58, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (82086063678571 / 100000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (2332212683013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12116_59 : CellCertificate 12116 (903760931486519 / 10000000000000000 : ℝ) (866819147474363 / 500000000000000000 : ℝ) (70202291979533 / 2000000000000000 : ℝ)
    (cell12116 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · norm_num [cell12116]
  · have h := gap_lower (n := 12116) (a := (4102615059931 / 5000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (233221666941 / 10000000000000 : ℝ))
      (E := (cell12116 ⟨59, by decide⟩).energy) (xi := (70202291979533 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12116 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12116]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12116])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12116) (a := (4102615059931 / 5000000000000 : ℝ)) (b := (4255210257 / 2500000000000 : ℝ)) (q := (233221666941 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12116])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12116]

theorem cert12117_40 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82697809516253 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2331979606141 / 100000000000000 : ℝ))
      (E := (cell12117 ⟨40, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82697809516253 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2331979606141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_41 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (8266362226087 / 10000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (466396717801 / 20000000000000 : ℝ))
      (E := (cell12117 ⟨41, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (8266362226087 / 10000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (466396717801 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_42 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82629458871277 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (582996892293 / 25000000000000 : ℝ))
      (E := (cell12117 ⟨42, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82629458871277 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (582996892293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_43 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82595319317321 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (233199160553 / 10000000000000 : ℝ))
      (E := (cell12117 ⟨43, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82595319317321 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (233199160553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_44 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82561203569003 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2331995580503 / 100000000000000 : ℝ))
      (E := (cell12117 ⟨44, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82561203569003 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2331995580503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_45 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (3301084463859 / 4000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (582999888129 / 25000000000000 : ℝ))
      (E := (cell12117 ⟨45, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (3301084463859 / 4000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (582999888129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_46 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (2062326084251 / 2500000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (583000894967 / 25000000000000 : ℝ))
      (E := (cell12117 ⟨46, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (2062326084251 / 2500000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (583000894967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_47 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (1649179977203 / 2000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (1166003772093 / 50000000000000 : ℝ))
      (E := (cell12117 ⟨47, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (1649179977203 / 2000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (1166003772093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_48 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82424978037409 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332011562181 / 100000000000000 : ℝ))
      (E := (cell12117 ⟨48, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82424978037409 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332011562181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_49 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82390980872567 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (46640310299 / 2000000000000 : ℝ))
      (E := (cell12117 ⟨49, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82390980872567 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (46640310299 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_50 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (41178503668261 / 50000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332019518869 / 100000000000000 : ℝ))
      (E := (cell12117 ⟨50, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (41178503668261 / 50000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332019518869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_51 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82323057400319 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332023513451 / 100000000000000 : ℝ))
      (E := (cell12117 ⟨51, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82323057400319 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332023513451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_52 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (20572282758787 / 25000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332027496873 / 100000000000000 : ℝ))
      (E := (cell12117 ⟨52, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (20572282758787 / 25000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332027496873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_53 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (16451045642469 / 20000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (466406305217 / 20000000000000 : ℝ))
      (E := (cell12117 ⟨53, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (16451045642469 / 20000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (466406305217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_54 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82221348903389 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332035480877 / 100000000000000 : ℝ))
      (E := (cell12117 ⟨54, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82221348903389 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332035480877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_55 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (2568359158747 / 3125000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (233203947679 / 10000000000000 : ℝ))
      (E := (cell12117 ⟨55, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (2568359158747 / 3125000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (233203947679 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_56 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82153660713653 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (1166021726079 / 50000000000000 : ℝ))
      (E := (cell12117 ⟨56, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82153660713653 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (1166021726079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_57 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (2566245368017 / 3125000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (1166023731591 / 50000000000000 : ℝ))
      (E := (cell12117 ⟨57, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (2566245368017 / 3125000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (1166023731591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_58 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (5130379140039 / 6250000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332051447727 / 100000000000000 : ℝ))
      (E := (cell12117 ⟨58, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (5130379140039 / 6250000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (2332051447727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12117_59 : CellCertificate 12117 (18074606951429 / 200000000000000 : ℝ) (1733495170766321 / 1000000000000000000 : ℝ) (21936360408857 / 625000000000000 : ℝ)
    (cell12117 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · norm_num [cell12117]
  · have h := gap_lower (n := 12117) (a := (82052304078081 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (116602773081 / 5000000000000 : ℝ))
      (E := (cell12117 ⟨59, by decide⟩).energy) (xi := (21936360408857 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12117 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12117]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12117])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12117) (a := (82052304078081 / 100000000000000 : ℝ)) (b := (170194187463 / 100000000000000 : ℝ)) (q := (116602773081 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12117])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12117]

theorem cert12118_40 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (2067445157259 / 2500000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331818531087 / 100000000000000 : ℝ))
      (E := (cell12118 ⟨40, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (2067445157259 / 2500000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331818531087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_41 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (16532723872069 / 20000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165911263947 / 50000000000000 : ℝ))
      (E := (cell12118 ⟨41, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (16532723872069 / 20000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165911263947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_42 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82629456295669 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (291478315347 / 12500000000000 : ℝ))
      (E := (cell12118 ⟨42, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82629456295669 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (291478315347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_43 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82595317066181 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (291478814483 / 12500000000000 : ℝ))
      (E := (cell12118 ⟨43, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82595317066181 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (291478814483 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_44 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (2064030041047 / 2500000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165917253537 / 50000000000000 : ℝ))
      (E := (cell12118 ⟨44, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (2064030041047 / 2500000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165917253537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_45 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82527109992921 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165919248047 / 50000000000000 : ℝ))
      (E := (cell12118 ⟨45, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82527109992921 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165919248047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_46 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (41246521044803 / 50000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331842482399 / 100000000000000 : ℝ))
      (E := (cell12118 ⟨46, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (41246521044803 / 50000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331842482399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_47 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (8245899790239 / 10000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (58296161631 / 2500000000000 : ℝ))
      (E := (cell12118 ⟨47, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (8245899790239 / 10000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (58296161631 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_48 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (20606244350469 / 25000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165925221827 / 50000000000000 : ℝ))
      (E := (cell12118 ⟨48, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (20606244350469 / 25000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165925221827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_49 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (16478196111763 / 20000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331854416461 / 100000000000000 : ℝ))
      (E := (cell12118 ⟨49, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (16478196111763 / 20000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331854416461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_50 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82357007344107 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (466371688237 / 20000000000000 : ℝ))
      (E := (cell12118 ⟨50, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82357007344107 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (466371688237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_51 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (20580764432199 / 25000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (116593122867 / 5000000000000 : ℝ))
      (E := (cell12118 ⟨51, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (20580764432199 / 25000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (116593122867 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_52 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (3291565267363 / 4000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331866404131 / 100000000000000 : ℝ))
      (E := (cell12118 ⟨52, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (3291565267363 / 4000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331866404131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_53 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82255229181279 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331870397431 / 100000000000000 : ℝ))
      (E := (cell12118 ⟨53, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82255229181279 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331870397431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_54 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82221350191889 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165937217529 / 50000000000000 : ℝ))
      (E := (cell12118 ⟨54, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82221350191889 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (1165937217529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_55 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (10273436835941 / 12500000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (116593919827 / 5000000000000 : ℝ))
      (E := (cell12118 ⟨55, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (10273436835941 / 12500000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (116593919827 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_56 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82153662639961 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (291485299657 / 12500000000000 : ℝ))
      (E := (cell12118 ⟨56, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82153662639961 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (291485299657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_57 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82119854021097 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331886375303 / 100000000000000 : ℝ))
      (E := (cell12118 ⟨57, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82119854021097 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (2331886375303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_58 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82086068802983 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (466378077339 / 20000000000000 : ℝ))
      (E := (cell12118 ⟨58, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82086068802983 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (466378077339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12118_59 : CellCertificate 12118 (90369976852577 / 1000000000000000 : ℝ) (866676035106901 / 500000000000000000 : ℝ) (70190415673081 / 2000000000000000 : ℝ)
    (cell12118 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · norm_num [cell12118]
  · have h := gap_lower (n := 12118) (a := (82052306957809 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (291486796133 / 12500000000000 : ℝ))
      (E := (cell12118 ⟨59, by decide⟩).energy) (xi := (70190415673081 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12118 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12118]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12118])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12118) (a := (82052306957809 / 100000000000000 : ℝ)) (b := (170179967061 / 100000000000000 : ℝ)) (q := (291486796133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12118])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12118]

theorem cert12119_40 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (82697803065507 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331657569577 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨40, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (82697803065507 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331657569577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_41 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (4133180823041 / 5000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (466332304341 / 20000000000000 : ℝ))
      (E := (cell12119 ⟨41, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (4133180823041 / 5000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (466332304341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_42 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (4131472686051 / 5000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (291458191421 / 12500000000000 : ℝ))
      (E := (cell12119 ⟨42, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (4131472686051 / 5000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (291458191421 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_43 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (82595314815957 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331669540011 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨43, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (82595314815957 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331669540011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_44 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (82561199715633 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (1165836773773 / 50000000000000 : ℝ))
      (E := (cell12119 ⟨44, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (82561199715633 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (1165836773773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_45 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (412635541951 / 500000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331677494861 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨45, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (412635541951 / 500000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331677494861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_46 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (16498608161993 / 20000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331681499009 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨46, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (16498608161993 / 20000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331681499009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_47 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (41229498472691 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331685500463 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨47, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (41229498472691 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331685500463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_48 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (41212488383527 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (116584474913 / 5000000000000 : ℝ))
      (E := (cell12119 ⟨48, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (41212488383527 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (116584474913 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_49 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (41195490122867 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331693491217 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨49, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (41195490122867 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331693491217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_50 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (41178503676161 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (1165848738969 / 50000000000000 : ℝ))
      (E := (cell12119 ⟨50, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (41178503676161 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (1165848738969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_51 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (82323058057863 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331701456809 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨51, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (82323058057863 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331701456809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_52 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (82289132333551 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331705484971 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨52, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (82289132333551 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331705484971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_53 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (82255230150721 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (291463680309 / 12500000000000 : ℝ))
      (E := (cell12119 ⟨53, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (82255230150721 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (291463680309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_54 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (10277668935107 / 12500000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (291464180627 / 12500000000000 : ℝ))
      (E := (cell12119 ⟨54, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (10277668935107 / 12500000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (291464180627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_55 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (41093748147789 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (582929357793 / 25000000000000 : ℝ))
      (E := (cell12119 ⟨55, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (41093748147789 / 50000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (582929357793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_56 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (641825504427 / 781250000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331721457323 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨56, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (641825504427 / 781250000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331721457323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_57 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (20529964066499 / 25000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331725402483 / 100000000000000 : ℝ))
      (E := (cell12119 ⟨57, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (20529964066499 / 25000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (2331725402483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_58 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (5130379460353 / 6250000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (582932360203 / 25000000000000 : ℝ))
      (E := (cell12119 ⟨58, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (5130379460353 / 6250000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (582932360203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12119_59 : CellCertificate 12119 (903669194348261 / 10000000000000000 : ℝ) (1733208993285319 / 1000000000000000000 : ℝ) (350922395367177 / 10000000000000000 : ℝ)
    (cell12119 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · norm_num [cell12119]
  · have h := gap_lower (n := 12119) (a := (82052309837801 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (466346678349 / 20000000000000 : ℝ))
      (E := (cell12119 ⟨59, by decide⟩).energy) (xi := (350922395367177 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12119 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12119]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12119])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12119) (a := (82052309837801 / 100000000000000 : ℝ)) (b := (170165749073 / 100000000000000 : ℝ)) (q := (466346678349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12119])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12119]

theorem cert12120_40 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (41348899920847 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331496721611 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨40, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (41348899920847 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331496721611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_41 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (82663613562293 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331500687859 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨41, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (82663613562293 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331500687859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_42 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (1291085174177 / 1562500000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (72859522263 / 3125000000000 : ℝ))
      (E := (cell12120 ⟨42, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (1291085174177 / 1562500000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (72859522263 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_43 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (1651906251333 / 2000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (233150867797 / 10000000000000 : ℝ))
      (E := (cell12120 ⟨43, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (1651906251333 / 2000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (233150867797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_44 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (4128059889513 / 5000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331512701921 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨44, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (4128059889513 / 5000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331512701921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_45 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (16505421357663 / 20000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331516666421 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨45, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (16505421357663 / 20000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331516666421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_46 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (41246519765559 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (1165760344263 / 50000000000000 : ℝ))
      (E := (cell12120 ⟨46, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (41246519765559 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (1165760344263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_47 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (41229497994563 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331524649857 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨47, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (41229497994563 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331524649857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_48 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (82424976132943 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (1165764333563 / 50000000000000 : ℝ))
      (E := (cell12120 ⟨48, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (82424976132943 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (1165764333563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_49 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (82390979933323 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (93261304857 / 4000000000000 : ℝ))
      (E := (cell12120 ⟨49, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (82390979933323 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (93261304857 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_50 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (41178503680583 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331536629129 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨50, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (41178503680583 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331536629129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_51 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (82323058387519 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331540629749 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨51, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (82323058387519 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331540629749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_52 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (41144566491787 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (116577231073 / 5000000000000 : ℝ))
      (E := (cell12120 ⟨52, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (41144566491787 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (116577231073 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_53 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (82255231120671 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331548602217 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨53, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (82255231120671 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331548602217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_54 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (82221352770289 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (145722039299 / 6250000000000 : ℝ))
      (E := (cell12120 ⟨54, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (82221352770289 / 100000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (145722039299 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_55 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (16437499580811 / 20000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (1165778290343 / 50000000000000 : ℝ))
      (E := (cell12120 ⟨55, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (16437499580811 / 20000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (1165778290343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_56 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (10269208311717 / 12500000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (23315605733 / 1000000000000 : ℝ))
      (E := (cell12120 ⟨56, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (10269208311717 / 12500000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (23315605733 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_57 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (2052996462781 / 2500000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (233156460381 / 10000000000000 : ℝ))
      (E := (cell12120 ⟨57, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (2052996462781 / 2500000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (233156460381 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_58 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (41043036964309 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331568550967 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨58, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (41043036964309 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331568550967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12120_59 : CellCertificate 12120 (180727725007541 / 2000000000000000 : ℝ) (866532969987511 / 500000000000000000 : ℝ) (70178543509093 / 2000000000000000 : ℝ)
    (cell12120 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · norm_num [cell12120]
  · have h := gap_lower (n := 12120) (a := (41026156359029 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331572588797 / 100000000000000 : ℝ))
      (E := (cell12120 ⟨59, by decide⟩).energy) (xi := (70178543509093 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12120 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12120]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12120])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12120) (a := (41026156359029 / 50000000000000 : ℝ)) (b := (170151533499 / 100000000000000 : ℝ)) (q := (2331572588797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12120])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12120]

theorem cert12121_40 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (41348898309461 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331335987189 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨40, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (41348898309461 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331335987189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_41 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (16532722132953 / 20000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (1165670013179 / 50000000000000 : ℝ))
      (E := (cell12121 ⟨41, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (16532722132953 / 20000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (1165670013179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_42 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (41314724287297 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331344007189 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨42, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (41314724287297 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331344007189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_43 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (41297655159129 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331347988501 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨43, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (41297655159129 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331347988501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_44 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (82561195865763 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (11656759851 / 500000000000 : ℝ))
      (E := (cell12121 ⟨44, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (82561195865763 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (11656759851 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_45 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (82527105187263 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (291419493997 / 12500000000000 : ℝ))
      (E := (cell12121 ⟨45, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (82527105187263 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (291419493997 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_46 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (82493038253063 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (23313599333 / 1000000000000 : ℝ))
      (E := (cell12121 ⟨46, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (82493038253063 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (23313599333 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_47 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (41229497516811 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331363972273 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨47, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (41229497516811 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331363972273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_48 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (10303121937443 / 12500000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (582841987563 / 25000000000000 : ℝ))
      (E := (cell12121 ⟨48, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (10303121937443 / 12500000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (582841987563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_49 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (41195489810791 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331371924881 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨49, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (41195489810791 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331371924881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_50 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (1029462592133 / 1250000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (29142199421 / 1250000000000 : ℝ))
      (E := (cell12121 ⟨50, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (1029462592133 / 1250000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (29142199421 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_51 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (82323058717763 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331379917219 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨51, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (82323058717763 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331379917219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_52 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (41144566817073 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (466276786307 / 20000000000000 : ℝ))
      (E := (cell12121 ⟨52, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (41144566817073 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (466276786307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_53 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (82255232091127 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331387876671 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨53, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (82255232091127 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331387876671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_54 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (8222135406019 / 10000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (582847967083 / 25000000000000 : ℝ))
      (E := (cell12121 ⟨54, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (8222135406019 / 10000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (582847967083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_55 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (82187499512959 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (582848976031 / 25000000000000 : ℝ))
      (E := (cell12121 ⟨55, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (82187499512959 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (582848976031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_56 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (41076834210601 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331399863313 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨56, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (41076834210601 / 50000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331399863313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_57 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (8211986075683 / 10000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (291425482639 / 12500000000000 : ℝ))
      (E := (cell12121 ⟨57, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (8211986075683 / 10000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (291425482639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_58 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (82086076491893 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331407894493 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨58, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (82086076491893 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331407894493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12121_59 : CellCertificate 12121 (903608060592887 / 10000000000000000 : ℝ) (216615363784633 / 125000000000000000 : ℝ) (70172608979741 / 2000000000000000 : ℝ)
    (cell12121 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · norm_num [cell12121]
  · have h := gap_lower (n := 12121) (a := (82052315598581 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331411841953 / 100000000000000 : ℝ))
      (E := (cell12121 ⟨59, by decide⟩).energy) (xi := (70172608979741 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12121 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12121]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12121])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12121) (a := (82052315598581 / 100000000000000 : ℝ)) (b := (85068660169 / 50000000000000 : ℝ)) (q := (2331411841953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12121])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12121]

theorem cert12122_40 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (82697793397189 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331175425003 / 100000000000000 : ℝ))
      (E := (cell12122 ⟨40, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (82697793397189 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331175425003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_41 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (16532721553647 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331179419787 / 100000000000000 : ℝ))
      (E := (cell12122 ⟨41, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (16532721553647 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331179419787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_42 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (645542546897 / 781250000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (582795853923 / 25000000000000 : ℝ))
      (E := (cell12122 ⟨42, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (645542546897 / 781250000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (582795853923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_43 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (82595308070783 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331187412849 / 100000000000000 : ℝ))
      (E := (cell12122 ⟨43, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (82595308070783 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331187412849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_44 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (4128059697107 / 5000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165595705583 / 50000000000000 : ℝ))
      (E := (cell12122 ⟨44, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (4128059697107 / 5000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165595705583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_45 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (20631775896761 / 25000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331195351527 / 100000000000000 : ℝ))
      (E := (cell12122 ⟨45, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (20631775896761 / 25000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331195351527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_46 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (82493036975801 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331199350987 / 100000000000000 : ℝ))
      (E := (cell12122 ⟨46, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (82493036975801 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331199350987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_47 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (8245899407887 / 10000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165601675007 / 50000000000000 : ℝ))
      (E := (cell12122 ⟨47, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (8245899407887 / 10000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165601675007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_48 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (16484994973371 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331207347643 / 100000000000000 : ℝ))
      (E := (cell12122 ⟨48, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (16484994973371 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331207347643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_49 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (5149436206907 / 6250000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (233121134269 / 10000000000000 : ℝ))
      (E := (cell12122 ⟨49, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (5149436206907 / 6250000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (233121134269 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_50 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (41178503690371 / 50000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165607666877 / 50000000000000 : ℝ))
      (E := (cell12122 ⟨50, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (41178503690371 / 50000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165607666877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_51 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (16464611809719 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165609659611 / 50000000000000 : ℝ))
      (E := (cell12122 ⟨51, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (16464611809719 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165609659611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_52 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (16457826857053 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165611648631 / 50000000000000 : ℝ))
      (E := (cell12122 ⟨52, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (16457826857053 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165611648631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_53 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (82255233062091 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (93249092993 / 4000000000000 : ℝ))
      (E := (cell12122 ⟨53, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (82255233062091 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (93249092993 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_54 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (82221355350557 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165615640847 / 50000000000000 : ℝ))
      (E := (cell12122 ⟨54, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (82221355350557 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165615640847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_55 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (5136718820143 / 6250000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (233123528341 / 10000000000000 : ℝ))
      (E := (cell12122 ⟨55, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (5136718820143 / 6250000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (233123528341 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_56 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (41076835174527 / 50000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165619634151 / 50000000000000 : ℝ))
      (E := (cell12122 ⟨56, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (41076835174527 / 50000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165619634151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_57 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (16423972600553 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165621646283 / 50000000000000 : ℝ))
      (E := (cell12122 ⟨57, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (16423972600553 / 20000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (1165621646283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_58 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (82086079055473 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331247294063 / 100000000000000 : ℝ))
      (E := (cell12122 ⟨58, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (82086079055473 / 100000000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331247294063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12122_59 : CellCertificate 12122 (903577501012589 / 10000000000000000 : ℝ) (866389952092799 / 500000000000000000 : ℝ) (175416688712667 / 5000000000000000 : ℝ)
    (cell12122 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · norm_num [cell12122]
  · have h := gap_lower (n := 12122) (a := (10256539809921 / 12500000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331251269487 / 100000000000000 : ℝ))
      (E := (cell12122 ⟨59, by decide⟩).energy) (xi := (175416688712667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12122 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12122]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12122])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12122) (a := (10256539809921 / 12500000000000 : ℝ)) (b := (42530777397 / 25000000000000 : ℝ)) (q := (2331251269487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12122])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12122]

theorem cert12123_40 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (16539558035299 / 20000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165507488183 / 50000000000000 : ℝ))
      (E := (cell12123 ⟨40, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (16539558035299 / 20000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165507488183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_41 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (82663604872703 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331018926853 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨41, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (82663604872703 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331018926853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_42 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (16525888686399 / 20000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331022937921 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨42, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (16525888686399 / 20000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331022937921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_43 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (82595305824223 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165513475507 / 50000000000000 : ℝ))
      (E := (cell12123 ⟨43, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (82595305824223 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165513475507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_44 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (1290018625303 / 1562500000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165515453629 / 50000000000000 : ℝ))
      (E := (cell12123 ⟨44, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (1290018625303 / 1562500000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165515453629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_45 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (82527101987659 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165517461939 / 50000000000000 : ℝ))
      (E := (cell12123 ⟨45, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (82527101987659 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165517461939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_46 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (20623258924833 / 25000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165519441379 / 50000000000000 : ℝ))
      (E := (cell12123 ⟨46, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (20623258924833 / 25000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165519441379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_47 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (20614748281217 / 25000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331042900781 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨47, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (20614748281217 / 25000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331042900781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_48 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (20606243558719 / 25000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331046859299 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨48, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (20606243558719 / 25000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331046859299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_49 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (8239097900011 / 10000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331050874853 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨49, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (8239097900011 / 10000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331050874853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_50 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (41178503695737 / 50000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331054887191 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨50, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (41178503695737 / 50000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331054887191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_51 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (5145191211251 / 6250000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165529417877 / 50000000000000 : ℝ))
      (E := (cell12123 ⟨51, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (5145191211251 / 6250000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165529417877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_52 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (20572283734233 / 25000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331062836577 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨52, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (20572283734233 / 25000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331062836577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_53 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (41127617016781 / 50000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (291383353587 / 12500000000000 : ℝ))
      (E := (cell12123 ⟨53, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (41127617016781 / 50000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (291383353587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_54 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (8222135664139 / 10000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331070868871 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨54, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (8222135664139 / 10000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331070868871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_55 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (82187502732043 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331074836623 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨55, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (82187502732043 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331074836623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_56 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (82153672277291 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (233107884733 / 10000000000000 : ℝ))
      (E := (cell12123 ⟨56, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (82153672277291 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (233107884733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_57 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (16423973049809 / 20000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (582770709771 / 25000000000000 : ℝ))
      (E := (cell12123 ⟨57, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (16423973049809 / 20000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (582770709771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_58 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (82086081619357 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331086808787 / 100000000000000 : ℝ))
      (E := (cell12123 ⟨58, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (82086081619357 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (2331086808787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12123_59 : CellCertificate 12123 (180709389259119 / 2000000000000000 : ℝ) (1732636921694781 / 1000000000000000000 : ℝ) (350803715123791 / 10000000000000000 : ℝ)
    (cell12123 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · norm_num [cell12123]
  · have h := gap_lower (n := 12123) (a := (82052321360419 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165545406131 / 50000000000000 : ℝ))
      (E := (cell12123 ⟨59, by decide⟩).energy) (xi := (350803715123791 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12123 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12123]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12123])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12123) (a := (82052321360419 / 100000000000000 : ℝ)) (b := (170108901251 / 100000000000000 : ℝ)) (q := (1165545406131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12123])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12123]

theorem cert12124_40 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (2067444673921 / 2500000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330854641281 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨40, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (2067444673921 / 2500000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330854641281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_41 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (82663601978169 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330858606271 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨41, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (82663601978169 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330858606271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_42 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (82629440862131 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165431286941 / 50000000000000 : ℝ))
      (E := (cell12124 ⟨42, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (82629440862131 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165431286941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_43 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (41297651789289 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330866603 / 100000000000 : ℝ))
      (E := (cell12124 ⟨43, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (41297651789289 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330866603 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_44 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (41280595048759 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330870576041 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨44, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (41280595048759 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330870576041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_45 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (82527100389107 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (93234982057 / 4000000000000 : ℝ))
      (E := (cell12124 ⟨45, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (82527100389107 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (93234982057 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_46 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (41246517211827 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330878587447 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨46, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (41246517211827 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330878587447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_47 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (41229496085809 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165441282863 / 50000000000000 : ℝ))
      (E := (cell12124 ⟨47, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (41229496085809 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165441282863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_48 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (10303121700451 / 12500000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (466177308819 / 20000000000000 : ℝ))
      (E := (cell12124 ⟨48, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (10303121700451 / 12500000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (466177308819 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_49 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (41195489345189 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (582722630343 / 25000000000000 : ℝ))
      (E := (cell12124 ⟨49, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (41195489345189 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (582722630343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_50 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (41178503701417 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165447277537 / 50000000000000 : ℝ))
      (E := (cell12124 ⟨50, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (41178503701417 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165447277537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_51 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (10290382464003 / 12500000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330898525767 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨51, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (10290382464003 / 12500000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330898525767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_52 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (41144567794573 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330902490517 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨52, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (41144567794573 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330902490517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_53 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (82255235005539 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330906506273 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨53, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (82255235005539 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330906506273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_54 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (82221357932689 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330910511833 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨54, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (82221357932689 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330910511833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_55 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (5136719021389 / 6250000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165457252363 / 50000000000000 : ℝ))
      (E := (cell12124 ⟨55, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (5136719021389 / 6250000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165457252363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_56 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (41076837102957 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330918482273 / 100000000000000 : ℝ))
      (E := (cell12124 ⟨56, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (41076837102957 / 50000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (2330918482273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_57 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (8211986749567 / 10000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (233092250067 / 10000000000000 : ℝ))
      (E := (cell12124 ⟨57, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (8211986749567 / 10000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (233092250067 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_58 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (82086084183547 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (145682906111 / 6250000000000 : ℝ))
      (E := (cell12124 ⟨58, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (82086084183547 / 100000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (145682906111 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12124_59 : CellCertificate 12124 (225879099110173 / 2500000000000000 : ℝ) (1732493962798771 / 1000000000000000000 : ℝ) (70154811598503 / 2000000000000000 : ℝ)
    (cell12124 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · norm_num [cell12124]
  · have h := gap_lower (n := 12124) (a := (16410464848347 / 20000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165465235141 / 50000000000000 : ℝ))
      (E := (cell12124 ⟨59, by decide⟩).energy) (xi := (70154811598503 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12124 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12124]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12124])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12124) (a := (16410464848347 / 20000000000000 : ℝ)) (b := (42523673831 / 25000000000000 : ℝ)) (q := (1165465235141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12124])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12124]

theorem cert12125_40 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (5168611483639 / 6250000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582673604937 / 25000000000000 : ℝ))
      (E := (cell12125 ⟨40, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (5168611483639 / 6250000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582673604937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_41 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (10332949885579 / 12500000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582674599833 / 25000000000000 : ℝ))
      (E := (cell12125 ⟨41, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (10332949885579 / 12500000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582674599833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_42 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (41314719146611 / 50000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330702382309 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨42, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (41314719146611 / 50000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330702382309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_43 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (10324412666731 / 12500000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330706368809 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨43, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (10324412666731 / 12500000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330706368809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_44 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (82561188176517 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (145669397421 / 6250000000000 : ℝ))
      (E := (cell12125 ⟨44, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (82561188176517 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (145669397421 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_45 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (82527098791387 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330714351777 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨45, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (82527098791387 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330714351777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_46 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (2577907285899 / 3125000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330718347399 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨46, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (2577907285899 / 3125000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330718347399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_47 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (82458991219119 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (46614446897 / 2000000000000 : ℝ))
      (E := (cell12125 ⟨47, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (82458991219119 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (46614446897 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_48 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (82424972973049 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (1165363171581 / 50000000000000 : ℝ))
      (E := (cell12125 ⟨48, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (82424972973049 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (1165363171581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_49 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (16478195676263 / 20000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330730341147 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨49, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (16478195676263 / 20000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330730341147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_50 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (41178503707411 / 50000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582683584351 / 25000000000000 : ℝ))
      (E := (cell12125 ⟨50, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (41178503707411 / 50000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582683584351 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_51 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (4116153002231 / 5000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582684582579 / 25000000000000 : ℝ))
      (E := (cell12125 ⟨51, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (4116153002231 / 5000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582684582579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_52 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (82289136241907 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330742318051 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨52, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (82289136241907 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330742318051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_53 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (82255235978023 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582686574641 / 25000000000000 : ℝ))
      (E := (cell12125 ⟨53, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (82255235978023 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582686574641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_54 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (16444271844891 / 20000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330750269597 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨54, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (16444271844891 / 20000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330750269597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_55 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (8218750595283 / 10000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330754287721 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨55, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (8218750595283 / 10000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330754287721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_56 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (82153676134921 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (116537914563 / 5000000000000 : ℝ))
      (E := (cell12125 ⟨56, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (82153676134921 / 100000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (116537914563 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_57 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (1026498371783 / 1250000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (93230491093 / 4000000000000 : ℝ))
      (E := (cell12125 ⟨57, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (1026498371783 / 1250000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (93230491093 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_58 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (2052152168701 / 2500000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330766242813 / 100000000000000 : ℝ))
      (E := (cell12125 ⟨58, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (2052152168701 / 2500000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (2330766242813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12125_59 : CellCertificate 12125 (451742925723331 / 5000000000000000 : ℝ) (108271939218233 / 62500000000000000 : ℝ) (70148881205989 / 2000000000000000 : ℝ)
    (cell12125 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · norm_num [cell12125]
  · have h := gap_lower (n := 12125) (a := (16410465424663 / 20000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582692560887 / 25000000000000 : ℝ))
      (E := (cell12125 ⟨59, by decide⟩).energy) (xi := (70148881205989 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12125 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12125) (a := (16410465424663 / 20000000000000 : ℝ)) (b := (170080491807 / 100000000000000 : ℝ)) (q := (582692560887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12125]

theorem cert12126_40 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (41348890260323 / 50000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330534311771 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨40, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (41348890260323 / 50000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330534311771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_41 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (20665899048023 / 25000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330538306037 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨41, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (20665899048023 / 25000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330538306037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_42 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (8262943572527 / 10000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330542304469 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨42, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (8262943572527 / 10000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330542304469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_43 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (82595299090033 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330546248439 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨43, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (82595299090033 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330546248439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_44 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (8256118625639 / 10000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330550255343 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨44, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (8256118625639 / 10000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330550255343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_45 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (165054194389 / 200000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (233055426613 / 10000000000000 : ℝ))
      (E := (cell12126 ⟨45, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (165054194389 / 200000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (233055426613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_46 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (82493031874673 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (1165279110721 / 50000000000000 : ℝ))
      (E := (cell12126 ⟨46, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (82493031874673 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (1165279110721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_47 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (8245899026737 / 10000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (466112447631 / 20000000000000 : ℝ))
      (E := (cell12126 ⟨47, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (8245899026737 / 10000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (466112447631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_48 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (103031215429 / 125000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (1165283128249 / 50000000000000 : ℝ))
      (E := (cell12126 ⟨48, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (103031215429 / 125000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (1165283128249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_49 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (82390978072921 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330570216383 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨49, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (82390978072921 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330570216383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_50 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (82357007427439 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330574234181 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨50, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (82357007427439 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330574234181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_51 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (20580765094451 / 25000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (291322273807 / 12500000000000 : ℝ))
      (E := (cell12126 ⟨51, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (20580765094451 / 25000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (291322273807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_52 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (16457827379043 / 20000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330582201241 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨52, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (16457827379043 / 20000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330582201241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_53 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (82255236951013 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330586205569 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨53, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (82255236951013 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330586205569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_54 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (41110680258343 / 50000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330590201181 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨54, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (41110680258343 / 50000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330590201181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_55 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (41093753781931 / 50000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330594185607 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨55, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (41093753781931 / 50000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330594185607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_56 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (41076839032157 / 50000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (582649539041 / 25000000000000 : ℝ))
      (E := (cell12126 ⟨56, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (41076839032157 / 50000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (582649539041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_57 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (16423974397991 / 20000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330602169049 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨57, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (16423974397991 / 20000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330602169049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_58 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (82086089312839 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330606162117 / 100000000000000 : ℝ))
      (E := (cell12126 ⟨58, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (82086089312839 / 100000000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (2330606162117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12126_59 : CellCertificate 12126 (903455311312293 / 10000000000000000 : ℝ) (346441623153563 / 200000000000000000 : ℝ) (350714759234523 / 10000000000000000 : ℝ)
    (cell12126 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · norm_num [cell12126]
  · have h := gap_lower (n := 12126) (a := (2051308250129 / 2500000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (116530506603 / 5000000000000 : ℝ))
      (E := (cell12126 ⟨59, by decide⟩).energy) (xi := (350714759234523 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12126 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12126) (a := (2051308250129 / 2500000000000 : ℝ)) (b := (1700662907 / 1000000000000 : ℝ)) (q := (116530506603 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12126]

theorem cert12127_40 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (41348888652053 / 50000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (46607486347 / 2000000000000 : ℝ))
      (E := (cell12127 ⟨40, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (41348888652053 / 50000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (46607486347 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_41 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82663593300549 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330378326387 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨41, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82663593300549 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330378326387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_42 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82629433158273 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330382281631 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨42, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82629433158273 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330382281631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_43 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (20648824211783 / 25000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330386300653 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨43, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (20648824211783 / 25000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330386300653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_44 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82561184337137 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330390265863 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨44, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82561184337137 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330390265863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_45 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (16505419119689 / 20000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (291299286811 / 12500000000000 : ℝ))
      (E := (cell12127 ⟨45, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (16505419119689 / 20000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (291299286811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_46 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (8249303060137 / 10000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (466079653681 / 20000000000000 : ℝ))
      (E := (cell12127 ⟨46, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (8249303060137 / 10000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (466079653681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_47 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (20614747329093 / 25000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (1165201122821 / 50000000000000 : ℝ))
      (E := (cell12127 ⟨47, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (20614747329093 / 25000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (1165201122821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_48 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82424971714061 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (291300785513 / 12500000000000 : ℝ))
      (E := (cell12127 ⟨48, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82424971714061 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (291300785513 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_49 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (20597744441299 / 25000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330410264877 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨49, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (20597744441299 / 25000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330410264877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_50 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82357007440683 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330414245409 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨50, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82357007440683 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330414245409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_51 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (3292922428463 / 4000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (29130227801 / 1250000000000 : ℝ))
      (E := (cell12127 ⟨51, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (3292922428463 / 4000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (29130227801 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_52 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82289137549069 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (582605564507 / 25000000000000 : ℝ))
      (E := (cell12127 ⟨52, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82289137549069 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (582605564507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_53 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82255237924509 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330426227291 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨53, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82255237924509 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330426227291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_54 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (41110680904691 / 50000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (466086037711 / 20000000000000 : ℝ))
      (E := (cell12127 ⟨54, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (41110680904691 / 50000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (466086037711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_55 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82187509175319 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (582608549597 / 25000000000000 : ℝ))
      (E := (cell12127 ⟨55, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82187509175319 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (582608549597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_56 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82153679994091 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (582609548779 / 25000000000000 : ℝ))
      (E := (cell12127 ⟨56, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82153679994091 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (582609548779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_57 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82119874237613 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (466088435169 / 20000000000000 : ℝ))
      (E := (cell12127 ⟨57, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82119874237613 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (466088435169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_58 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (82086091877941 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330446196583 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨58, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (82086091877941 / 100000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330446196583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12127_59 : CellCertificate 12127 (903424776036369 / 10000000000000000 : ℝ) (866032613810597 / 500000000000000000 : ℝ) (35068511760469 / 1000000000000000 : ℝ)
    (cell12127 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · norm_num [cell12127]
  · have h := gap_lower (n := 12127) (a := (20513083221817 / 25000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330450194957 / 100000000000000 : ℝ))
      (E := (cell12127 ⟨59, by decide⟩).energy) (xi := (35068511760469 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12127 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12127) (a := (20513083221817 / 25000000000000 : ℝ)) (b := (85026046001 / 50000000000000 : ℝ)) (q := (2330450194957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12127]

theorem cert12128_40 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (20674443522151 / 25000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (93208579807 / 4000000000000 : ℝ))
      (E := (cell12128 ⟨40, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (20674443522151 / 25000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (93208579807 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_41 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (82663590410003 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330218460387 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨41, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (82663590410003 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330218460387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_42 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (82629430592231 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (1165111215633 / 50000000000000 : ℝ))
      (E := (cell12128 ⟨42, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (82629430592231 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (1165111215633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_43 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (41297647302573 / 50000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (1165113233347 / 50000000000000 : ℝ))
      (E := (cell12128 ⟨43, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (41297647302573 / 50000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (1165113233347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_44 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (20640295604689 / 25000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330230449083 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨44, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (20640295604689 / 25000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330230449083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_45 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (82527094003223 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (582558609213 / 25000000000000 : ℝ))
      (E := (cell12128 ⟨45, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (82527094003223 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (582558609213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_46 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (41246514664429 / 50000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (291279803683 / 12500000000000 : ℝ))
      (E := (cell12128 ⟨46, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (41246514664429 / 50000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (291279803683 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_47 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (20614747091531 / 25000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (1165121213083 / 50000000000000 : ℝ))
      (E := (cell12128 ⟨47, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (20614747091531 / 25000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (1165121213083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_48 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (82424971085631 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (1165123212993 / 50000000000000 : ℝ))
      (E := (cell12128 ⟨48, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (82424971085631 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (1165123212993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_49 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (82390977458139 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (291281303467 / 12500000000000 : ℝ))
      (E := (cell12128 ⟨49, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (82390977458139 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (291281303467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_50 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (16471401490911 / 20000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330254371089 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨50, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (16471401490911 / 20000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330254371089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_51 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (20580765261483 / 25000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330258372247 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨51, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (20580765261483 / 25000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330258372247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_52 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (8228913820347 / 10000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330262370477 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨52, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (8228913820347 / 10000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330262370477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_53 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (82255238898511 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330266363733 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨53, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (82255238898511 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330266363733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_54 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (5138835193909 / 6250000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330270349753 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨54, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (5138835193909 / 6250000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330270349753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_55 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (25683597121 / 31250000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330274385107 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨55, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (25683597121 / 31250000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330274385107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_56 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (82153681924253 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330278349053 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨56, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (82153681924253 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330278349053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_57 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (5132492280351 / 6250000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (582570589201 / 25000000000000 : ℝ))
      (E := (cell12128 ⟨57, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (5132492280351 / 6250000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (582570589201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_58 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (82086094443347 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330286346213 / 100000000000000 : ℝ))
      (E := (cell12128 ⟨58, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (82086094443347 / 100000000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (2330286346213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12128_59 : CellCertificate 12128 (225848561404419 / 2500000000000000 : ℝ) (1731922363046033 / 1000000000000000000 : ℝ) (350655481138889 / 10000000000000000 : ℝ)
    (cell12128 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · norm_num [cell12128]
  · have h := gap_lower (n := 12128) (a := (2051308394241 / 2500000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (233029031397 / 10000000000000 : ℝ))
      (E := (cell12128 ⟨59, by decide⟩).energy) (xi := (350655481138889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12128 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12128) (a := (2051308394241 / 2500000000000 : ℝ)) (b := (170037895711 / 100000000000000 : ℝ)) (q := (233029031397 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12128]

theorem cert12129_40 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (4134888543707 / 5000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330054727871 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨40, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (4134888543707 / 5000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330054727871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_41 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (20665896880113 / 25000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (582514677009 / 25000000000000 : ℝ))
      (E := (cell12129 ⟨41, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (20665896880113 / 25000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (582514677009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_42 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (10328678503393 / 12500000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330062753373 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨42, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (10328678503393 / 12500000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330062753373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_43 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82595292364073 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330066746563 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨43, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82595292364073 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330066746563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_44 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (322504611333 / 390625000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330070687439 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨44, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (322504611333 / 390625000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330070687439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_45 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82527092408831 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330074693223 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨45, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82527092408831 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330074693223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_46 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (5155814253571 / 6250000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (116503935231 / 5000000000000 : ℝ))
      (E := (cell12129 ⟨46, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (5155814253571 / 6250000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (116503935231 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_47 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (659671899333 / 800000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330082662023 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨47, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (659671899333 / 800000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330082662023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_48 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (8242497045791 / 10000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330086682141 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨48, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (8242497045791 / 10000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330086682141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_49 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (329563908607 / 400000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330090646059 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨49, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (329563908607 / 400000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330090646059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_50 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (16471401493811 / 20000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330094670143 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨50, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (16471401493811 / 20000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330094670143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_51 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82323061380877 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (1165049317477 / 50000000000000 : ℝ))
      (E := (cell12129 ⟨51, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82323061380877 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (1165049317477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_52 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82289138858417 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (93204106261 / 4000000000000 : ℝ))
      (E := (cell12129 ⟨52, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82289138858417 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (93204106261 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_53 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82255239873019 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (582526653723 / 25000000000000 : ℝ))
      (E := (cell12129 ⟨53, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82255239873019 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (582526653723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_54 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82221364396171 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330110625759 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨54, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82221364396171 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330110625759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_55 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82187512399507 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330114627681 / 100000000000000 : ℝ))
      (E := (cell12129 ⟨55, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82187512399507 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (2330114627681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_56 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82153683854799 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (93204744719 / 4000000000000 : ℝ))
      (E := (cell12129 ⟨56, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82153683854799 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (93204744719 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_57 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82119878733963 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (582530648437 / 25000000000000 : ℝ))
      (E := (cell12129 ⟨57, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82119878733963 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (582530648437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_58 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (82086097009057 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (582531652751 / 25000000000000 : ℝ))
      (E := (cell12129 ⟨58, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (82086097009057 / 100000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (582531652751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12129_59 : CellCertificate 12129 (903363720055003 / 10000000000000000 : ℝ) (1731779522036499 / 1000000000000000000 : ℝ) (87656462458891 / 2500000000000000 : ℝ)
    (cell12129 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · norm_num [cell12129]
  · have h := gap_lower (n := 12129) (a := (20513084663069 / 25000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (291266325921 / 12500000000000 : ℝ))
      (E := (cell12129 ⟨59, by decide⟩).energy) (xi := (87656462458891 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12129 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12129) (a := (20513084663069 / 25000000000000 : ℝ)) (b := (170023701829 / 100000000000000 : ℝ)) (q := (291266325921 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12129]

theorem cert12130_40 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (10337220957589 / 12500000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164947566409 / 50000000000000 : ℝ))
      (E := (cell12130 ⟨40, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (10337220957589 / 12500000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164947566409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_41 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82663584631897 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329899128047 / 100000000000000 : ℝ))
      (E := (cell12130 ⟨41, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82663584631897 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329899128047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_42 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (20657356365753 / 25000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329903130487 / 100000000000000 : ℝ))
      (E := (cell12130 ⟨42, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (20657356365753 / 25000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329903130487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_43 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82595290123913 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164953540753 / 50000000000000 : ℝ))
      (E := (cell12130 ⟨43, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82595290123913 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164953540753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_44 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (20640294646153 / 25000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329911098497 / 100000000000000 : ℝ))
      (E := (cell12130 ⟨44, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (20640294646153 / 25000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329911098497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_45 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82527090815271 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (291239390301 / 12500000000000 : ℝ))
      (E := (cell12130 ⟨45, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82527090815271 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (291239390301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_46 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (16498605357241 / 20000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164959546937 / 50000000000000 : ℝ))
      (E := (cell12130 ⟨46, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (16498605357241 / 20000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164959546937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_47 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (20614746616969 / 25000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (58248076773 / 2500000000000 : ℝ))
      (E := (cell12130 ⟨47, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (20614746616969 / 25000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (58248076773 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_48 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82424969830897 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (93197082103 / 4000000000000 : ℝ))
      (E := (cell12130 ⟨48, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82424969830897 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (93197082103 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_49 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82390976846029 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329931037647 / 100000000000000 : ℝ))
      (E := (cell12130 ⟨49, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82390976846029 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329931037647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_50 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82357007484181 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164967541827 / 50000000000000 : ℝ))
      (E := (cell12130 ⟨50, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82357007484181 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164967541827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_51 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (10290382714551 / 12500000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (145621191947 / 6250000000000 : ℝ))
      (E := (cell12130 ⟨51, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (10290382714551 / 12500000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (145621191947 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_52 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82289139513909 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (291242882151 / 12500000000000 : ℝ))
      (E := (cell12130 ⟨52, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82289139513909 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (291242882151 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_53 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82255240848031 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329947039769 / 100000000000000 : ℝ))
      (E := (cell12130 ⟨53, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82255240848031 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329947039769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_54 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82221365690263 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (18202742317 / 781250000000 : ℝ))
      (E := (cell12130 ⟨54, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82221365690263 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (18202742317 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_55 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82187514012237 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (582488761049 / 25000000000000 : ℝ))
      (E := (cell12130 ⟨55, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82187514012237 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (582488761049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_56 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82153685785729 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164979500943 / 50000000000000 : ℝ))
      (E := (cell12130 ⟨56, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82153685785729 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (1164979500943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_57 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (41059940491327 / 50000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329963004857 / 100000000000000 : ℝ))
      (E := (cell12130 ⟨57, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (41059940491327 / 50000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329963004857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_58 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (82086099575071 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329966990961 / 100000000000000 : ℝ))
      (E := (cell12130 ⟨58, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (82086099575071 / 100000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329966990961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12130_59 : CellCertificate 12130 (451666599673567 / 5000000000000000 : ℝ) (1731636704586761 / 1000000000000000000 : ℝ) (175298111846579 / 5000000000000000 : ℝ)
    (cell12130 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · norm_num [cell12130]
  · have h := gap_lower (n := 12130) (a := (3282093661407 / 4000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329971016021 / 100000000000000 : ℝ))
      (E := (cell12130 ⟨59, by decide⟩).energy) (xi := (175298111846579 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12130 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12130) (a := (3282093661407 / 4000000000000 : ℝ)) (b := (170009510353 / 100000000000000 : ℝ)) (q := (2329971016021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12130]

theorem cert12131_40 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (82697764448321 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329735651329 / 100000000000000 : ℝ))
      (E := (cell12131 ⟨40, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (82697764448321 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329735651329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_41 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (41331790872169 / 50000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329739661711 / 100000000000000 : ℝ))
      (E := (cell12131 ⟨41, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (41331790872169 / 50000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329739661711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_42 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (41314711449917 / 50000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (72804488167 / 3125000000000 : ℝ))
      (E := (cell12131 ⟨42, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (41314711449917 / 50000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (72804488167 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_43 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (41297643942333 / 50000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329747647797 / 100000000000000 : ℝ))
      (E := (cell12131 ⟨43, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (41297643942333 / 50000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329747647797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_44 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (5160073541803 / 6250000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (582437905869 / 25000000000000 : ℝ))
      (E := (cell12131 ⟨44, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (5160073541803 / 6250000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (582437905869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_45 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (82527089222543 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329755606799 / 100000000000000 : ℝ))
      (E := (cell12131 ⟨45, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (82527089222543 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329755606799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_46 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (2577907047377 / 3125000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (582439899307 / 25000000000000 : ℝ))
      (E := (cell12131 ⟨46, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (2577907047377 / 3125000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (582439899307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_47 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (20614746379969 / 25000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329763594007 / 100000000000000 : ℝ))
      (E := (cell12131 ⟨47, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (20614746379969 / 25000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329763594007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_48 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (82424969204593 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164883798081 / 50000000000000 : ℝ))
      (E := (cell12131 ⟨48, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (82424969204593 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164883798081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_49 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (5149436033811 / 6250000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164885801251 / 50000000000000 : ℝ))
      (E := (cell12131 ⟨49, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (5149436033811 / 6250000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164885801251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_50 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (16471401499987 / 20000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164887776349 / 50000000000000 : ℝ))
      (E := (cell12131 ⟨50, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (16471401499987 / 20000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164887776349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_51 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (3292922482101 / 4000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (46595591259 / 2000000000000 : ℝ))
      (E := (cell12131 ⟨51, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (3292922482101 / 4000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (46595591259 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_52 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (20572285042487 / 25000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (582445893131 / 25000000000000 : ℝ))
      (E := (cell12131 ⟨52, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (20572285042487 / 25000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (582445893131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_53 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (1645104836471 / 2000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164893760187 / 50000000000000 : ℝ))
      (E := (cell12131 ⟨53, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (1645104836471 / 2000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164893760187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_54 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (4111068349241 / 5000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164895761103 / 50000000000000 : ℝ))
      (E := (cell12131 ⟨54, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (4111068349241 / 5000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (1164895761103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_55 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (82187515625393 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329795516571 / 100000000000000 : ℝ))
      (E := (cell12131 ⟨55, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (82187515625393 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329795516571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_56 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (82153687717043 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329799500787 / 100000000000000 : ℝ))
      (E := (cell12131 ⟨56, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (82153687717043 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (2329799500787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_57 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (82119883231689 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (582450882761 / 25000000000000 : ℝ))
      (E := (cell12131 ⟨57, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (82119883231689 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (582450882761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_58 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (20521525535347 / 25000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (465961497217 / 20000000000000 : ℝ))
      (E := (cell12131 ⟨58, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (20521525535347 / 25000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (465961497217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12131_59 : CellCertificate 12131 (451651341746429 / 5000000000000000 : ℝ) (1731493910690991 / 1000000000000000000 : ℝ) (87641650677529 / 2500000000000000 : ℝ)
    (cell12131 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · norm_num [cell12131]
  · have h := gap_lower (n := 12131) (a := (82052344418337 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (465962296159 / 20000000000000 : ℝ))
      (E := (cell12131 ⟨59, by decide⟩).energy) (xi := (87641650677529 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12131 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12131) (a := (82052344418337 / 100000000000000 : ℝ)) (b := (169995321283 / 100000000000000 : ℝ)) (q := (465962296159 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12131]

theorem cert12132_40 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (41348880618483 / 50000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (465915256681 / 20000000000000 : ℝ))
      (E := (cell12132 ⟨40, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (41348880618483 / 50000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (465915256681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_41 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (41331789428887 / 50000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329580250319 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨41, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (41331789428887 / 50000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329580250319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_42 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82629420337609 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (58239607117 / 2500000000000 : ℝ))
      (E := (cell12132 ⟨42, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82629420337609 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (58239607117 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_43 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82595285646333 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164794134581 / 50000000000000 : ℝ))
      (E := (cell12132 ⟨43, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82595285646333 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164794134581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_44 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (20640293688489 / 25000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164796131189 / 50000000000000 : ℝ))
      (E := (cell12132 ⟨44, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (20640293688489 / 25000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164796131189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_45 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (16505417526129 / 20000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329596264007 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨45, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (16505417526129 / 20000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329596264007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_46 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (10311628030839 / 12500000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (465920042937 / 20000000000000 : ℝ))
      (E := (cell12132 ⟨46, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (10311628030839 / 12500000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (465920042937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_47 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (659671876581 / 800000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (465920846257 / 20000000000000 : ℝ))
      (E := (cell12132 ⟨47, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (659671876581 / 800000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (465920846257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_48 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82424968578997 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329608195153 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨48, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82424968578997 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329608195153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_49 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (8239097623659 / 10000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329612222827 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨49, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (8239097623659 / 10000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329612222827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_50 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (20589251879079 / 25000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164808097561 / 50000000000000 : ℝ))
      (E := (cell12132 ⟨50, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (20589251879079 / 25000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164808097561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_51 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82323062389229 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164810084647 / 50000000000000 : ℝ))
      (E := (cell12132 ⟨51, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82323062389229 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164810084647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_52 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (20572285206633 / 25000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (582406050619 / 25000000000000 : ℝ))
      (E := (cell12132 ⟨52, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (20572285206633 / 25000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (582406050619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_53 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82255242799573 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329628174699 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨53, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82255242799573 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329628174699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_54 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82221368279841 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164816100833 / 50000000000000 : ℝ))
      (E := (cell12132 ⟨54, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82221368279841 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (1164816100833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_55 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (20546879309743 / 25000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329636162889 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨55, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (20546879309743 / 25000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329636162889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_56 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82153689648741 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329640173743 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨56, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82153689648741 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329640173743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_57 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82119885481067 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329644172311 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨57, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82119885481067 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329644172311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_58 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (10260763088501 / 12500000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (72801504859 / 3125000000000 : ℝ))
      (E := (cell12132 ⟨58, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (10260763088501 / 12500000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (72801504859 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12132_59 : CellCertificate 12132 (903272172490963 / 10000000000000000 : ℝ) (1731351140343363 / 1000000000000000000 : ℝ) (175268493442443 / 5000000000000000 : ℝ)
    (cell12132 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · norm_num [cell12132]
  · have h := gap_lower (n := 12132) (a := (82052347301763 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329652119959 / 100000000000000 : ℝ))
      (E := (cell12132 ⟨59, by decide⟩).energy) (xi := (175268493442443 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12132 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12132) (a := (82052347301763 / 100000000000000 : ℝ)) (b := (169981134619 / 100000000000000 : ℝ)) (q := (2329652119959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12132]

theorem cert12133_40 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (10337219753331 / 12500000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329417029047 / 100000000000000 : ℝ))
      (E := (cell12133 ⟨40, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (10337219753331 / 12500000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329417029047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_41 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (16532715194441 / 20000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (465884202259 / 20000000000000 : ℝ))
      (E := (cell12133 ⟨41, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (16532715194441 / 20000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (465884202259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_42 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82629417776339 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329425003027 / 100000000000000 : ℝ))
      (E := (cell12133 ⟨42, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82629417776339 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329425003027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_43 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (5162205213057 / 6250000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329429004363 / 100000000000000 : ℝ))
      (E := (cell12133 ⟨43, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (5162205213057 / 6250000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329429004363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_44 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (161252290703 / 195312500000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (465886603041 / 20000000000000 : ℝ))
      (E := (cell12133 ⟨44, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (161252290703 / 195312500000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (465886603041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_45 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82527086039577 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (93177479057 / 4000000000000 : ℝ))
      (E := (cell12133 ⟨45, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82527086039577 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (93177479057 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_46 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82493022978151 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (145590062817 / 6250000000000 : ℝ))
      (E := (cell12133 ⟨46, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82493022978151 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (145590062817 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_47 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82458983626123 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (465888996551 / 20000000000000 : ℝ))
      (E := (cell12133 ⟨47, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82458983626123 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (465888996551 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_48 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82424967954109 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164724483651 / 50000000000000 : ℝ))
      (E := (cell12133 ⟨48, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82424967954109 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164724483651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_49 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (10298871991609 / 12500000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164726478761 / 50000000000000 : ℝ))
      (E := (cell12133 ⟨49, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (10298871991609 / 12500000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164726478761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_50 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (41178503766661 / 50000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (291182119001 / 12500000000000 : ℝ))
      (E := (cell12133 ⟨50, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (41178503766661 / 50000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (291182119001 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_51 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (41161531363259 / 50000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164730474567 / 50000000000000 : ℝ))
      (E := (cell12133 ⟨51, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (41161531363259 / 50000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164730474567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_52 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82289141483661 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164732473533 / 50000000000000 : ℝ))
      (E := (cell12133 ⟨52, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82289141483661 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164732473533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_53 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82255243776101 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329468943749 / 100000000000000 : ℝ))
      (E := (cell12133 ⟨53, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82255243776101 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329468943749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_54 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82221369575327 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329472936923 / 100000000000000 : ℝ))
      (E := (cell12133 ⟨54, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82221369575327 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329472936923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_55 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (3287500754119 / 4000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (145592307757 / 6250000000000 : ℝ))
      (E := (cell12133 ⟨55, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (3287500754119 / 4000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (145592307757 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_56 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82153691580823 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164740451313 / 50000000000000 : ℝ))
      (E := (cell12133 ⟨56, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82153691580823 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164740451313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_57 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82119887730789 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164742464329 / 50000000000000 : ℝ))
      (E := (cell12133 ⟨57, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82119887730789 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (1164742464329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_58 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (20521526818733 / 25000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329488880949 / 100000000000000 : ℝ))
      (E := (cell12133 ⟨58, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (20521526818733 / 25000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329488880949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

theorem cert12133_59 : CellCertificate 12133 (903241666340237 / 10000000000000000 : ℝ) (1731208393538053 / 1000000000000000000 : ℝ) (350507376215913 / 10000000000000000 : ℝ)
    (cell12133 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · norm_num [cell12133]
  · have h := gap_lower (n := 12133) (a := (82052350185451 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329492874383 / 100000000000000 : ℝ))
      (E := (cell12133 ⟨59, by decide⟩).energy) (xi := (350507376215913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12133 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12133) (a := (82052350185451 / 100000000000000 : ℝ)) (b := (4249173759 / 2500000000000 : ℝ)) (q := (2329492874383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12133]

end BstLean.Part281
