import BstLean.Part268CellShard18Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12800_40 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41347916324149 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119760507931 / 50000000000000 : ℝ))
      (E := (cell12800 ⟨40, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41347916324149 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119760507931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_41 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41330929213417 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239525037399 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨41, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41330929213417 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239525037399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_42 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (82627907776587 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239529021351 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨42, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (82627907776587 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239529021351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_43 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41296990333971 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239533025531 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨43, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41296990333971 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239533025531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_44 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (8256007707143 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239537048781 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨44, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (8256007707143 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239537048781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_45 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41263098478867 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (34992828607 / 1562500000000 : ℝ))
      (E := (cell12800 ⟨45, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41263098478867 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (34992828607 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_46 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (20623085074421 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (447909005793 / 20000000000000 : ℝ))
      (E := (cell12800 ⟨46, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (20623085074421 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (447909005793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_47 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (82458507062253 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559887260331 / 25000000000000 : ℝ))
      (E := (cell12800 ⟨47, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (82458507062253 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559887260331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_48 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (20606174305641 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119776532951 / 50000000000000 : ℝ))
      (E := (cell12800 ⟨48, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (20606174305641 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119776532951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_49 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (82390910749883 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239557100463 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨49, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (82390910749883 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239557100463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_50 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (4117857380781 / 5000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (447912216713 / 20000000000000 : ℝ))
      (E := (cell12800 ⟨50, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (4117857380781 / 5000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (447912216713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_51 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (82323407791327 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239565071493 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨51, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (82323407791327 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239565071493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_52 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (822896912487 / 1000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559892280103 / 25000000000000 : ℝ))
      (E := (cell12800 ⟨52, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (822896912487 / 1000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559892280103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_53 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (82255997959577 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239573109187 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨53, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (82255997959577 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239573109187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_54 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41111163947967 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (111978854677 / 5000000000000 : ℝ))
      (E := (cell12800 ⟨54, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41111163947967 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (111978854677 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_55 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (8218868102989 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239581129079 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨55, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (8218868102989 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239581129079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_56 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (82155057333701 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (22395850939 / 1000000000000 : ℝ))
      (E := (cell12800 ⟨56, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (82155057333701 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (22395850939 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_57 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41060728389881 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (279948637791 / 12500000000000 : ℝ))
      (E := (cell12800 ⟨57, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41060728389881 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (279948637791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_58 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (16417575868121 / 20000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239593150311 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨58, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (16417575868121 / 20000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239593150311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_59 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (820543249889 / 1000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239597174387 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨59, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (820543249889 / 1000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239597174387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12801_40 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (258424468951 / 312500000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559850382961 / 25000000000000 : ℝ))
      (E := (cell12801 ⟨40, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (258424468951 / 312500000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559850382961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_41 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41330928070941 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559851373607 / 25000000000000 : ℝ))
      (E := (cell12801 ⟨41, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41330928070941 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559851373607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_42 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82627905790249 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239409537677 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨42, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82627905790249 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239409537677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_43 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16518795795961 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239413543063 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨43, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16518795795961 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239413543063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_44 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16512015136217 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239417509353 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨44, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16512015136217 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239417509353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_45 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82526195864771 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239421552847 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨45, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82526195864771 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239421552847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_46 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82492339501693 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119712777113 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨46, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82492339501693 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119712777113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_47 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41229253281413 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239429570533 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨47, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41229253281413 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239429570533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_48 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82424697019293 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119716770399 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨48, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82424697019293 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119716770399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_49 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (2059772771059 / 2500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (44788751613 / 2000000000000 : ℝ))
      (E := (cell12801 ⟨49, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (2059772771059 / 2500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (44788751613 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_50 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82357148003439 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119720784863 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨50, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82357148003439 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119720784863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_51 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41161704237041 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (223944556431 / 10000000000000 : ℝ))
      (E := (cell12801 ⟨51, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41161704237041 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (223944556431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_52 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82289692225987 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (279931195191 / 12500000000000 : ℝ))
      (E := (cell12801 ⟨52, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82289692225987 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (279931195191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_53 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82255999230991 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239453617359 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨53, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82255999230991 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239453617359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_54 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (5138895591317 / 6250000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (223945761041 / 10000000000000 : ℝ))
      (E := (cell12801 ⟨54, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (5138895591317 / 6250000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (223945761041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_55 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82188682888349 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239461596217 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨55, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82188682888349 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239461596217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_56 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41077529742539 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559866407551 / 25000000000000 : ℝ))
      (E := (cell12801 ⟨56, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41077529742539 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559866407551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_57 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (10265182402957 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239469649367 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨57, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (10265182402957 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239469649367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_58 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (10260985259577 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239473649581 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨58, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (10260985259577 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239473649581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_59 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41027164008313 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119738813259 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨59, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41027164008313 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119738813259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12802_40 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (20673956870297 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119641022371 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨40, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (20673956870297 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119641022371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_41 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82661853857741 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239286007191 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨41, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82661853857741 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239286007191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_42 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41313951902343 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239290050993 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨42, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41313951902343 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239290050993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_43 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (10324247161551 / 12500000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111964702881 / 5000000000000 : ℝ))
      (E := (cell12802 ⟨43, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (10324247161551 / 12500000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111964702881 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_44 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (20640018572861 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119649012919 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨44, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (20640018572861 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119649012919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_45 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (3301047790899 / 4000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119651035973 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨45, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (3301047790899 / 4000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119651035973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_46 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82492338706333 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (17914448613 / 800000000000 : ℝ))
      (E := (cell12802 ⟨46, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82492338706333 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (17914448613 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_47 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41229253031997 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (447862019383 / 20000000000000 : ℝ))
      (E := (cell12802 ⟨47, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41229253031997 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (447862019383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_48 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82424696816581 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (279914258981 / 12500000000000 : ℝ))
      (E := (cell12802 ⟨48, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82424696816581 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (279914258981 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_49 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41195455467681 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119659029041 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨49, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41195455467681 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119659029041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_50 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82357148391747 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239322112161 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨50, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82357148391747 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239322112161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_51 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (20580852289323 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111966305673 / 5000000000000 : ℝ))
      (E := (cell12802 ⟨51, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (20580852289323 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111966305673 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_52 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82289693203693 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (89573204723 / 4000000000000 : ℝ))
      (E := (cell12802 ⟨52, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82289693203693 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (89573204723 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_53 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82256000502789 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119667061461 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨53, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82256000502789 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119667061461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_54 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41111165513279 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239338124707 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨54, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41111165513279 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239338124707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_55 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (1027358559339 / 1250000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (279917764991 / 12500000000000 : ℝ))
      (E := (cell12802 ⟨55, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (1027358559339 / 1250000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (279917764991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_56 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82155061636733 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119673082003 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨56, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82155061636733 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119673082003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_57 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82121461667793 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119675067391 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨57, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82121461667793 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119675067391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_58 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41043942406417 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111967707321 / 5000000000000 : ℝ))
      (E := (cell12802 ⟨58, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41043942406417 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111967707321 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_59 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (3282173241781 / 4000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239358135459 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨59, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (3282173241781 / 4000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239358135459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12803_40 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (10336978112363 / 12500000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559790638639 / 25000000000000 : ℝ))
      (E := (cell12803 ⟨40, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (10336978112363 / 12500000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559790638639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_41 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (8266185157441 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239166575689 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨41, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (8266185157441 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239166575689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_42 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82627901819897 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (22391705613 / 1000000000000 : ℝ))
      (E := (cell12803 ⟨42, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82627901819897 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (22391705613 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_43 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (330375902423 / 400000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447834913841 / 20000000000000 : ℝ))
      (E := (cell12803 ⟨43, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (330375902423 / 400000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447834913841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_44 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41280036451253 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239178598237 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨44, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41280036451253 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239178598237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_45 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82526193680847 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447836517629 / 20000000000000 : ℝ))
      (E := (cell12803 ⟨45, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82526193680847 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447836517629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_46 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41246168955803 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239186596159 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨46, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41246168955803 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239186596159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_47 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82458505565759 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (223919062047 / 10000000000000 : ℝ))
      (E := (cell12803 ⟨47, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82458505565759 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (223919062047 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_48 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82424696614431 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239194600107 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨48, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82424696614431 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239194600107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_49 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82390911028889 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239198650697 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨49, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82390911028889 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239198650697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_50 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (16471429756109 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119601325939 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨50, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (16471429756109 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119601325939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_51 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (20580852460239 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239206659929 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨51, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (20580852460239 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239206659929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_52 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82289694181817 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119605335989 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨52, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82289694181817 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119605335989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_53 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (8225600177497 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119607342469 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨53, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (8225600177497 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119607342469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_54 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (10277791574049 / 12500000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239218695517 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨54, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (10277791574049 / 12500000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239218695517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_55 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (16437737321241 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (223922270021 / 10000000000000 : ℝ))
      (E := (cell12803 ⟨55, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (16437737321241 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (223922270021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_56 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41077531894333 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239226695307 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨56, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41077531894333 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239226695307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_57 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82121464112173 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239230676889 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨57, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82121464112173 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239230676889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_58 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82087887549259 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559808675003 / 25000000000000 : ℝ))
      (E := (cell12803 ⟨58, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82087887549259 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559808675003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_59 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82054334072597 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239238701209 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨59, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82054334072597 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239238701209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12804_40 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (16539164463493 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559760794701 / 25000000000000 : ℝ))
      (E := (cell12804 ⟨40, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (16539164463493 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559760794701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_41 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (8266184929189 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239047141141 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨41, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (8266184929189 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239047141141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_42 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82627899835883 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239051186207 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨42, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82627899835883 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239051186207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_43 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82593973919831 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239055195473 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨43, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82593973919831 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239055195473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_44 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (8256007151427 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239059167703 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨44, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (8256007151427 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239059167703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_45 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41263096294943 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239063160321 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨45, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41263096294943 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239063160321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_46 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82492337117509 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239067171731 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨46, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82492337117509 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239067171731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_47 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (2061462626703 / 2500000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239071200121 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨47, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (2061462626703 / 2500000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239071200121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_48 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (2060617410321 / 2500000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239075184523 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨48, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (2060617410321 / 2500000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239075184523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_49 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (4119545556147 / 5000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239079240561 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨49, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (4119545556147 / 5000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239079240561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_50 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82357149169833 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (223908324787 / 10000000000000 : ℝ))
      (E := (cell12804 ⟨50, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82357149169833 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (223908324787 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_51 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82323410525073 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119543601859 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨51, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82323410525073 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119543601859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_52 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82289695160361 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447818244647 / 20000000000000 : ℝ))
      (E := (cell12804 ⟨52, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82289695160361 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447818244647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_53 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41128001523767 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239095244347 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨53, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41128001523767 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239095244347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_54 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (3288893366343 / 4000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447819852751 / 20000000000000 : ℝ))
      (E := (cell12804 ⟨54, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (3288893366343 / 4000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447819852751 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_55 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41094344232801 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119551638979 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨55, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41094344232801 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119551638979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_56 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82155065940877 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119553641621 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨56, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82155065940877 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119553641621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_57 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (16424293311359 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (223911127569 / 10000000000000 : ℝ))
      (E := (cell12804 ⟨57, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (16424293311359 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (223911127569 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_58 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82087890285893 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119557655177 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨58, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82087890285893 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119557655177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_59 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82054337100841 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (279889908071 / 12500000000000 : ℝ))
      (E := (cell12804 ⟨59, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82054337100841 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (279889908071 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12805_40 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82695819736873 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238923741213 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨40, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82695819736873 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238923741213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_41 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (4133092350509 / 5000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223892776233 / 10000000000000 : ℝ))
      (E := (cell12805 ⟨41, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (4133092350509 / 5000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223892776233 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_42 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82627897852643 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238931808107 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨42, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82627897852643 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238931808107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_43 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (1651879444693 / 2000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119467879971 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨43, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (1651879444693 / 2000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119467879971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_44 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82560070126737 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (447787958617 / 20000000000000 : ℝ))
      (E := (cell12805 ⟨44, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82560070126737 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (447787958617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_45 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (10315773937449 / 12500000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238943788473 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨45, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (10315773937449 / 12500000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238943788473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_46 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16498467264809 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238947803339 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨46, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16498467264809 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238947803339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_47 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (20614626142769 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223895183587 / 10000000000000 : ℝ))
      (E := (cell12805 ⟨47, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (20614626142769 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223895183587 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_48 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (8242469621181 / 10000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (447791165019 / 20000000000000 : ℝ))
      (E := (cell12805 ⟨48, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (8242469621181 / 10000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (447791165019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_49 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (20597727804379 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (279869978459 / 12500000000000 : ℝ))
      (E := (cell12805 ⟨49, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (20597727804379 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (279869978459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_50 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82357149559609 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559740960287 / 25000000000000 : ℝ))
      (E := (cell12805 ⟨50, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82357149559609 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559740960287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_51 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16464682241929 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119483931429 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨51, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16464682241929 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119483931429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_52 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41144848069661 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223897183089 / 10000000000000 : ℝ))
      (E := (cell12805 ⟨52, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41144848069661 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223897183089 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_53 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41128002160241 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223897586021 / 10000000000000 : ℝ))
      (E := (cell12805 ⟨53, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41128002160241 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223897586021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_54 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16444467145021 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559744972127 / 25000000000000 : ℝ))
      (E := (cell12805 ⟨54, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16444467145021 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559744972127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_55 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82188690325313 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238983853169 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨55, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82188690325313 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238983853169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_56 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16431013618673 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238987868677 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨56, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16431013618673 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238987868677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_57 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (4106073450083 / 5000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119495936013 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨57, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (4106073450083 / 5000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119495936013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_58 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82087893022733 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223899591827 / 10000000000000 : ℝ))
      (E := (cell12805 ⟨58, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82087893022733 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223899591827 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_59 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41027170064629 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119499942369 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨59, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41027170064629 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119499942369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12806_40 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82695817157127 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (447760883611 / 20000000000000 : ℝ))
      (E := (cell12806 ⟨40, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82695817157127 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (447760883611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_41 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (258318264779 / 312500000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (447761687851 / 20000000000000 : ℝ))
      (E := (cell12806 ⟨41, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (258318264779 / 312500000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (447761687851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_42 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82627895870177 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238812426999 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨42, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82627895870177 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238812426999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_43 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82593970550207 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238816439097 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨43, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82593970550207 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238816439097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_44 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82560068739907 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559705103883 / 25000000000000 : ℝ))
      (E := (cell12806 ⟨44, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82560068739907 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559705103883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_45 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (20631547602491 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (69963262929 / 3125000000000 : ℝ))
      (E := (cell12806 ⟨45, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (20631547602491 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (69963262929 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_46 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82492335531211 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119414216043 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨46, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82492335531211 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119414216043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_47 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82458504074627 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119416234397 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨47, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82458504074627 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119416234397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_48 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82424696011339 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238836462879 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨48, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82424696011339 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238836462879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_49 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82390911312617 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238840470999 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨49, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82390911312617 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238840470999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_50 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (658857199599 / 800000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238844490701 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨50, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (658857199599 / 800000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238844490701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_51 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (8232341189467 / 10000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (139928028769 / 6250000000000 : ℝ))
      (E := (cell12806 ⟨51, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (8232341189467 / 10000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (139928028769 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_52 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (41144848559351 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (111942624747 / 5000000000000 : ℝ))
      (E := (cell12806 ⟨52, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (41144848559351 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (111942624747 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_53 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (20564001398453 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238856473467 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨53, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (20564001398453 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238856473467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_54 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82222337291983 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (223886051069 / 10000000000000 : ℝ))
      (E := (cell12806 ⟨54, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82222337291983 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (223886051069 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_55 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (16437738437067 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559716121239 / 25000000000000 : ℝ))
      (E := (cell12806 ⟨55, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (16437738437067 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559716121239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_56 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (8215507024613 / 10000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238868510747 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨56, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (8215507024613 / 10000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238868510747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_57 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (41060735723383 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238872525057 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨57, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (41060735723383 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238872525057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_58 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82087895759781 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119438261879 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨58, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82087895759781 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119438261879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_59 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (41027171578923 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119440280861 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨59, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (41027171578923 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119440280861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12807_40 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (41347907289113 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119342545909 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨40, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (41347907289113 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119342545909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_41 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82661842449189 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238689054357 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨41, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82661842449189 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238689054357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_42 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (16525578777697 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238693101689 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨42, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (16525578777697 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238693101689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_43 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (41296984433251 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119348557641 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨43, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (41296984433251 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119348557641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_44 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82560067353779 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238701093899 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨44, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82560067353779 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238701093899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_45 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82526189321003 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238705094961 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨45, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82526189321003 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238705094961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_46 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (1288942730297 / 1562500000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238709116871 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨46, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (1288942730297 / 1562500000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238709116871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_47 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (41229251789387 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447742619779 / 20000000000000 : ℝ))
      (E := (cell12807 ⟨47, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (41229251789387 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447742619779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_48 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82424695811429 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238717156821 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨48, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82424695811429 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238717156821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_49 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (41195455704121 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (279840138947 / 12500000000000 : ℝ))
      (E := (cell12807 ⟨49, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (41195455704121 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (279840138947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_50 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82357150340629 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238725137541 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨50, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82357150340629 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238725137541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_51 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (20580853145037 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238729173103 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨51, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (20580853145037 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238729173103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_52 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (164579396197 / 200000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559683289087 / 25000000000000 : ℝ))
      (E := (cell12807 ⟨52, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (164579396197 / 200000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559683289087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_53 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (3290240274701 / 4000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (111936857159 / 5000000000000 : ℝ))
      (E := (cell12807 ⟨53, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (3290240274701 / 4000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (111936857159 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_54 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (10277792357401 / 12500000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559685297347 / 25000000000000 : ℝ))
      (E := (cell12807 ⟨54, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (10277792357401 / 12500000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559685297347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_55 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (8218869404567 / 10000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119372586659 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨55, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (8218869404567 / 10000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119372586659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_56 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82155072399173 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559687302363 / 25000000000000 : ℝ))
      (E := (cell12807 ⟨56, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82155072399173 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559687302363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_57 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (16424294778423 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119376587813 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨57, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (16424294778423 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119376587813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_58 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (20521974624259 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119378593 / 50000000000 : ℝ))
      (E := (cell12807 ⟨58, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (20521974624259 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119378593 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_59 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82054346186607 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447752247263 / 20000000000000 : ℝ))
      (E := (cell12807 ⟨59, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82054346186607 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447752247263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12808_40 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (8269581200017 / 10000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (279820720313 / 12500000000000 : ℝ))
      (E := (cell12808 ⟨40, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (8269581200017 / 10000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (279820720313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_41 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (20665460042477 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238569783979 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨41, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (20665460042477 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238569783979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_42 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41313945953783 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (17908590187 / 800000000000 : ℝ))
      (E := (cell12808 ⟨42, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41313945953783 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (17908590187 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_43 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (16518793436707 / 20000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238577788499 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨43, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (16518793436707 / 20000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238577788499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_44 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (82560065968353 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447716365637 / 20000000000000 : ℝ))
      (E := (cell12808 ⟨44, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (82560065968353 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447716365637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_45 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (20631547058177 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (89543433287 / 4000000000000 : ℝ))
      (E := (cell12808 ⟨45, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (20631547058177 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (89543433287 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_46 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (20623083486859 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119294899399 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨46, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (20623083486859 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119294899399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_47 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (82458503083517 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (139912115251 / 6250000000000 : ℝ))
      (E := (cell12808 ⟨47, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (82458503083517 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (139912115251 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_48 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41212347806039 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119298923989 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨48, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41212347806039 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119298923989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_49 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (82390911504391 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238601808373 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨49, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (82390911504391 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238601808373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_50 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (2573660960371 / 3125000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238605840659 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨50, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (2573660960371 / 3125000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238605840659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_51 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (514521332913 / 625000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238609824209 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨51, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (514521332913 / 625000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238609824209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_52 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (16457939815743 / 20000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447722774831 / 20000000000000 : ℝ))
      (E := (cell12808 ⟨52, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (16457939815743 / 20000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447722774831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_53 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (82256008141621 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (279827233669 / 12500000000000 : ℝ))
      (E := (cell12808 ⟨53, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (82256008141621 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (279827233669 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_54 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (82222340426781 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119310932759 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨54, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (82222340426781 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119310932759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_55 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (82188695906317 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (559656464787 / 25000000000000 : ℝ))
      (E := (cell12808 ⟨55, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (82188695906317 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (559656464787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_56 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (20538768638123 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238629905661 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨56, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (20538768638123 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238629905661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_57 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41060738168853 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (223863388289 / 10000000000000 : ℝ))
      (E := (cell12808 ⟨57, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41060738168853 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (223863388289 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_58 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41043950617249 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119318952499 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨58, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41043950617249 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119318952499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_59 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (4102717460777 / 5000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119320954259 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨59, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (4102717460777 / 5000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119320954259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12809_40 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (1033697617787 / 1250000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559611622217 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨40, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (1033697617787 / 1250000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559611622217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_41 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (20665459472859 / 25000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238450510561 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨41, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (20665459472859 / 25000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238450510561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_42 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82627889927421 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238454500861 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨42, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82627889927421 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238454500861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_43 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (16518793100261 / 20000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (279807314697 / 12500000000000 : ℝ))
      (E := (cell12809 ⟨43, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (16518793100261 / 20000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (279807314697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_44 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82560064583629 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (139903906293 / 6250000000000 : ℝ))
      (E := (cell12809 ⟨44, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82560064583629 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (139903906293 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_45 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (2063154678627 / 2500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119233253809 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨45, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (2063154678627 / 2500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119233253809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_46 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (41246166578247 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119235268383 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨46, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (41246166578247 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119235268383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_47 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82458502588853 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (447694905479 / 20000000000000 : ℝ))
      (E := (cell12809 ⟨47, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82458502588853 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (447694905479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_48 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (41212347706643 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (44769570727 / 2000000000000 : ℝ))
      (E := (cell12809 ⟨48, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (41212347706643 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (44769570727 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_49 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (10298863950133 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238482561389 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨49, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (10298863950133 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238482561389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_50 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82357151123603 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (447697308213 / 20000000000000 : ℝ))
      (E := (cell12809 ⟨50, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82357151123603 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (447697308213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_51 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (5145213372029 / 6250000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (139905661917 / 6250000000000 : ℝ))
      (E := (cell12809 ⟨51, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (5145213372029 / 6250000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (139905661917 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_52 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82289700059349 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238494589321 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨52, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82289700059349 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238494589321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_53 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (822560094161 / 1000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238498592919 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨53, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (822560094161 / 1000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238498592919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_54 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82222341994701 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119251299083 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨54, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82222341994701 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119251299083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_55 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (20547174441819 / 25000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559626650389 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨55, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (20547174441819 / 25000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559626650389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_56 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82155076706089 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238510599373 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨56, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82155076706089 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238510599373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_57 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82121478783539 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559628661713 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨57, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82121478783539 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559628661713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_58 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (41043951986083 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559629655393 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨58, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (41043951986083 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559629655393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_59 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (16410870448929 / 20000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238522637537 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨59, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (16410870448929 / 20000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238522637537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12810_40 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41347903423297 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238327270913 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨40, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41347903423297 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238327270913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_41 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (82661835613773 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238331292883 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨41, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (82661835613773 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238331292883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_42 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (82627887948049 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238335284147 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨42, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (82627887948049 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238335284147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_43 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (82593963819813 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119169651257 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨43, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (82593963819813 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119169651257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_44 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41280031599803 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447668657593 / 20000000000000 : ℝ))
      (E := (cell12810 ⟨44, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41280031599803 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447668657593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_45 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (82526186058117 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119173648959 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨45, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (82526186058117 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119173648959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_46 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41246166183091 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559587817969 / 25000000000000 : ℝ))
      (E := (cell12810 ⟨46, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41246166183091 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559587817969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_47 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (16491700418957 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559588831449 / 25000000000000 : ℝ))
      (E := (cell12810 ⟨47, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (16491700418957 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559588831449 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_48 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (82424695215053 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559589834957 / 25000000000000 : ℝ))
      (E := (cell12810 ⟨48, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (82424695215053 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559589834957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_49 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (4119545584913 / 5000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238363311657 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨49, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (4119545584913 / 5000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238363311657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_50 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (82357151515823 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238367297751 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨50, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (82357151515823 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238367297751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_51 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41161707319651 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238371354457 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨51, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41161707319651 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238371354457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_52 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (205724252601 / 250000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238375360887 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨52, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (205724252601 / 250000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238375360887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_53 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (1028200133637 / 1250000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119189686473 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨53, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (1028200133637 / 1250000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119189686473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_54 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (10277792945371 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238383328247 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨54, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (10277792945371 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238383328247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_55 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (20547174907137 / 25000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238387341431 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨55, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (20547174907137 / 25000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238387341431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_56 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41077539429981 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238391349723 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨56, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41077539429981 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238391349723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_57 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41060740614807 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (69949856511 / 3125000000000 : ℝ))
      (E := (cell12810 ⟨57, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41060740614807 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (69949856511 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_58 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41043953355021 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238399394901 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨58, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41043953355021 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238399394901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_59 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41027177636961 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238403423371 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨59, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41027177636961 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238403423371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12811_40 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82695804271073 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119104024941 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨40, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82695804271073 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119104024941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_41 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82661833336919 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (447642414433 / 20000000000000 : ℝ))
      (E := (cell12811 ⟨41, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82661833336919 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (447642414433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_42 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82627885969449 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (139888504027 / 6250000000000 : ℝ))
      (E := (cell12811 ⟨42, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82627885969449 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (139888504027 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_43 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41296981069529 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119110042243 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨43, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41296981069529 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119110042243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_44 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (20640015454071 / 25000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279778009039 / 12500000000000 : ℝ))
      (E := (cell12811 ⟨44, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (20640015454071 / 25000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279778009039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_45 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (4126309248591 / 5000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (89529123413 / 4000000000000 : ℝ))
      (E := (cell12811 ⟨45, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (4126309248591 / 5000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (89529123413 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_46 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82492331576501 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559558015757 / 25000000000000 : ℝ))
      (E := (cell12811 ⟨46, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82492331576501 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559558015757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_47 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82458501601311 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238236121377 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨47, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82458501601311 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238236121377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_48 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82424695017379 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279780010197 / 12500000000000 : ℝ))
      (E := (cell12811 ⟨48, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82424695017379 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279780010197 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_49 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (4119545589799 / 5000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238244118147 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨49, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (4119545589799 / 5000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238244118147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_50 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82357151908531 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119124055359 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨50, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82357151908531 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119124055359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_51 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (643151682239 / 781250000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238252115567 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨51, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (643151682239 / 781250000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238252115567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_52 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (20572425505467 / 25000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119128064907 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨52, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (20572425505467 / 25000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119128064907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_53 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82256011966203 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238260150369 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨53, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82256011966203 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238260150369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_54 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41111172565791 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238264114847 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨54, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41111172565791 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238264114847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_55 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (8218870149013 / 10000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238268137887 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨55, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (8218870149013 / 10000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238268137887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_56 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (2567346281691 / 3125000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238272156711 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨56, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (2567346281691 / 3125000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238272156711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_57 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (8212148367593 / 10000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (447655233479 / 20000000000000 : ℝ))
      (E := (cell12811 ⟨57, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (8212148367593 / 10000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (447655233479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_58 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (20521977362031 / 25000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (139892510363 / 6250000000000 : ℝ))
      (E := (cell12811 ⟨58, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (20521977362031 / 25000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (139892510363 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_59 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (8205435830337 / 10000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119142103409 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨59, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (8205435830337 / 10000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119142103409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12812_40 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (20673950424099 / 25000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447617776907 / 20000000000000 : ℝ))
      (E := (cell12812 ⟨40, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (20673950424099 / 25000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447617776907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_41 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82661831060873 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238092848409 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨41, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82661831060873 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238092848409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_42 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82627883991623 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119048450259 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨42, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82627883991623 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119048450259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_43 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82593960459039 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119050431747 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨43, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82593960459039 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119050431747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_44 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (322500236069 / 390625000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119052456291 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨44, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (322500236069 / 390625000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119052456291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_45 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (20631545971547 / 25000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238108869841 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨45, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (20631545971547 / 25000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238108869841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_46 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82492330787449 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (139882056889 / 6250000000000 : ℝ))
      (E := (cell12812 ⟨46, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82492330787449 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (139882056889 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_47 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82458501108431 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (111905845707 / 5000000000000 : ℝ))
      (E := (cell12812 ⟨47, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82458501108431 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (111905845707 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_48 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (10303086852533 / 12500000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238120938433 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨48, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (10303086852533 / 12500000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238120938433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_49 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82390911894223 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (223812492189 / 10000000000000 : ℝ))
      (E := (cell12812 ⟨49, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82390911894223 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (223812492189 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_50 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (41178576150863 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (139883057561 / 6250000000000 : ℝ))
      (E := (cell12812 ⟨50, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (41178576150863 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (139883057561 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_51 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (16464683202867 / 20000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (111906646651 / 5000000000000 : ℝ))
      (E := (cell12812 ⟨51, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (16464683202867 / 20000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (111906646651 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_52 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (41144851501877 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238136955143 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨52, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (41144851501877 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238136955143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_53 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (20564003310457 / 25000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238140925191 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨53, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (20564003310457 / 25000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238140925191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_54 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82222346700543 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (139884059873 / 6250000000000 : ℝ))
      (E := (cell12812 ⟨54, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82222346700543 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (139884059873 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_55 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (3287548134081 / 4000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238148990923 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨55, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (3287548134081 / 4000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238148990923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_56 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82155083168539 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119076480603 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨56, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82155083168539 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119076480603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_57 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (10265185765311 / 12500000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (69942405723 / 3125000000000 : ℝ))
      (E := (cell12812 ⟨57, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (10265185765311 / 12500000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (69942405723 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_58 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82087912186413 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (34971265523 / 1562500000000 : ℝ))
      (E := (cell12812 ⟨58, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82087912186413 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (34971265523 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_59 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (8205436133299 / 10000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119082493939 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨59, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (8205436133299 / 10000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119082493939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12813_40 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82695799122563 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (139873107257 / 6250000000000 : ℝ))
      (E := (cell12813 ⟨40, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82695799122563 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (139873107257 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_41 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (16532365757127 / 20000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237973739179 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨41, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (16532365757127 / 20000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237973739179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_42 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (10328485251821 / 12500000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559494433401 / 25000000000000 : ℝ))
      (E := (cell12813 ⟨42, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (10328485251821 / 12500000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559494433401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_43 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82593958779757 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237981757193 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨43, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82593958779757 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237981757193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_44 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (16512011810349 / 20000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237985749923 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨44, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (16512011810349 / 20000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237985749923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_45 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (41263091400611 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118994884607 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨45, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (41263091400611 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118994884607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_46 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82492329999027 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237993754563 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨46, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82492329999027 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237993754563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_47 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (41229250308073 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559499440751 / 25000000000000 : ℝ))
      (E := (cell12813 ⟨47, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (41229250308073 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559499440751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_48 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (20606173655927 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2238001733561 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨48, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (20606173655927 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2238001733561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_49 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (8239091199299 / 10000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447601156371 / 20000000000000 : ℝ))
      (E := (cell12813 ⟨49, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (8239091199299 / 10000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447601156371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_50 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (8235715269541 / 10000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1119004893757 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨50, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (8235715269541 / 10000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1119004893757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_51 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (8232341670253 / 10000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447602761363 / 20000000000000 : ℝ))
      (E := (cell12813 ⟨51, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (8232341670253 / 10000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447602761363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_52 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82289703986057 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1119008888917 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨52, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82289703986057 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1119008888917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_53 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (41128007258917 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1119010907769 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨53, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (41128007258917 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1119010907769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_54 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (1644446965397 / 2000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2238025798523 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨54, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (1644446965397 / 2000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2238025798523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_55 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82188705214231 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559507460357 / 25000000000000 : ℝ))
      (E := (cell12813 ⟨55, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82188705214231 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559507460357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_56 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (41077542661621 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (111901691117 / 5000000000000 : ℝ))
      (E := (cell12813 ⟨56, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (41077542661621 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (111901691117 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_57 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82121488569287 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (279754731947 / 12500000000000 : ℝ))
      (E := (cell12813 ⟨57, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82121488569287 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (279754731947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_58 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (20521978731227 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447608363743 / 20000000000000 : ℝ))
      (E := (cell12813 ⟨58, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (20521978731227 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447608363743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_59 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82054364362781 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2238045825757 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨59, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82054364362781 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2238045825757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12814_40 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41347898274787 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118925301687 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨40, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41347898274787 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118925301687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_41 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (16532365302241 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (223785456813 / 10000000000000 : ℝ))
      (E := (cell12814 ⟨41, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (16532365302241 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (223785456813 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_42 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41313940019143 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (69933081953 / 3125000000000 : ℝ))
      (E := (cell12814 ⟨42, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41313940019143 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (69933081953 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_43 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (20648489275303 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237862589101 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨43, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (20648489275303 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237862589101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_44 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41280028835263 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237866584339 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨44, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41280028835263 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237866584339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_45 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82526181716921 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237870606823 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨45, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82526181716921 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237870606823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_46 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (16498465842247 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237874596049 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨46, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (16498465842247 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237874596049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_47 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41229250062227 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118939304527 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨47, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41229250062227 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118939304527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_48 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (8242469442771 / 10000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118941321901 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨48, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (8242469442771 / 10000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118941321901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_49 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82390912092279 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118943319539 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨49, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82390912092279 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118943319539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_50 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (4117857654479 / 5000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (559472662837 / 25000000000000 : ℝ))
      (E := (cell12814 ⟨50, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (4117857654479 / 5000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (559472662837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_51 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41161708695589 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118947338969 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨51, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41161708695589 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118947338969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_52 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (10286213121097 / 12500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (223789865693 / 10000000000000 : ℝ))
      (E := (cell12814 ⟨52, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (10286213121097 / 12500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (223789865693 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_53 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82256015794223 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118951322111 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨53, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82256015794223 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118951322111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_54 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (5138896864969 / 6250000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118953347801 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨54, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (5138896864969 / 6250000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118953347801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_55 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82188707076749 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118955344703 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨55, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82188707076749 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118955344703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_56 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41077543739111 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118957340491 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨56, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41077543739111 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118957340491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_57 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (10265186377041 / 12500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237918725561 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨57, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (10265186377041 / 12500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237918725561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_58 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82087917663609 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237922700719 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨58, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82087917663609 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237922700719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_59 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (10256795924093 / 12500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (447585344091 / 20000000000000 : ℝ))
      (E := (cell12814 ⟨59, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (10256795924093 / 12500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (447585344091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12815_40 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82695793977429 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237731487563 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨40, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82695793977429 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237731487563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_41 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82661824237583 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237735511609 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨41, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82661824237583 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237735511609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_42 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (10328484757847 / 12500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237739508387 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨42, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (10328484757847 / 12500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237739508387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_43 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82593955423403 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118871767851 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨43, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82593955423403 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118871767851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_44 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (10320007036251 / 12500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559436883383 / 25000000000000 : ℝ))
      (E := (cell12815 ⟨44, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (10320007036251 / 12500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559436883383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_45 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20631545158321 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237751500417 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨45, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20631545158321 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237751500417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_46 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82492328424071 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237755552481 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨46, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82492328424071 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237755552481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_47 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20614624908339 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237759511207 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨47, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20614624908339 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237759511207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_48 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (8242469423227 / 10000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111888177563 / 5000000000000 : ℝ))
      (E := (cell12815 ⟨48, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (8242469423227 / 10000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111888177563 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_49 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82390912192091 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559441888131 / 25000000000000 : ℝ))
      (E := (cell12815 ⟨49, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82390912192091 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559441888131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_50 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82357153484239 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237771571463 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨50, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82357153484239 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237771571463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_51 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82323418080277 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237775546389 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨51, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82323418080277 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237775546389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_52 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (10286213243989 / 12500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237779592429 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨52, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (10286213243989 / 12500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237779592429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_53 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (5141001066937 / 6250000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237783588433 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨53, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (5141001066937 / 6250000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237783588433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_54 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (16444470281901 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (447557518023 / 20000000000000 : ℝ))
      (E := (cell12815 ⟨54, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (16444470281901 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (447557518023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_55 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82188708939577 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237791593967 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨55, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82188708939577 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237791593967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_56 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82155089633477 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237795596267 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨56, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82155089633477 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237795596267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_57 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82121493463609 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237799593089 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨57, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82121493463609 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237799593089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_58 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82087920402517 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237803639481 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨58, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82087920402517 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237803639481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_59 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41027185211439 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (69931487899 / 3125000000000 : ℝ))
      (E := (cell12815 ⟨59, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41027185211439 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (69931487899 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12816_40 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82695791406127 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118806213719 / 50000000000000 : ℝ))
      (E := (cell12816 ⟨40, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82695791406127 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118806213719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_41 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82661821964769 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237616452051 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨41, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82661821964769 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237616452051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_42 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82627876088037 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447524090017 / 20000000000000 : ℝ))
      (E := (cell12816 ⟨42, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82627876088037 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447524090017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_43 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82593953746329 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237624420513 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨43, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82593953746329 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237624420513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_44 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (8256005491019 / 10000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237628420947 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨44, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (8256005491019 / 10000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237628420947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_45 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (10315772443789 / 12500000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237632449997 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨45, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (10315772443789 / 12500000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237632449997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_46 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82492327637537 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237636447159 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨46, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82492327637537 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237636447159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_47 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82458499142851 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237640469467 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨47, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82458499142851 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237640469467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_48 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (20606173509347 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237644455939 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨48, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (20606173509347 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237644455939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_49 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (3295636491697 / 4000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237648463227 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨49, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (3295636491697 / 4000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237648463227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_50 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (10294644234923 / 12500000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279706561109 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨50, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (10294644234923 / 12500000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279706561109 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_51 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (20580854692457 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447531294237 / 20000000000000 : ℝ))
      (E := (cell12816 ⟨51, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (20580854692457 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447531294237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_52 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (16457941387093 / 20000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559415131323 / 25000000000000 : ℝ))
      (E := (cell12816 ⟨52, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (16457941387093 / 20000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559415131323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_53 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82256018348143 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559416132511 / 25000000000000 : ℝ))
      (E := (cell12816 ⟨53, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82256018348143 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559416132511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_54 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82222352979851 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237668541153 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨54, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82222352979851 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237668541153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_55 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82188710802717 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237672495999 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨55, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82188710802717 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237672495999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_56 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82155091789009 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118838254529 / 50000000000000 : ℝ))
      (E := (cell12816 ⟨56, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82155091789009 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118838254529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_57 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (20530373977783 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118840258659 / 50000000000000 : ℝ))
      (E := (cell12816 ⟨57, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (20530373977783 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118840258659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_58 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (8208792314163 / 10000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (89507383033 / 4000000000000 : ℝ))
      (E := (cell12816 ⟨58, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (8208792314163 / 10000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (89507383033 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_59 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82054373453183 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237688561901 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨59, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82054373453183 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237688561901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12817_40 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20673947208917 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237493364243 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨40, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20673947208917 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237493364243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_41 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82661819692761 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (111874869473 / 5000000000000 : ℝ))
      (E := (cell12817 ⟨41, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82661819692761 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (111874869473 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_42 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (8262787411407 / 10000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447500277757 / 20000000000000 : ℝ))
      (E := (cell12817 ⟨42, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (8262787411407 / 10000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447500277757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_43 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (10324244008749 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237505420021 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨43, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (10324244008749 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237505420021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_44 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (1290000836423 / 1562500000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237509423143 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨44, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (1290000836423 / 1562500000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237509423143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_45 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20631544617001 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237513396691 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨45, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20631544617001 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237513396691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_46 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82492326851631 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237517397887 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨46, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82492326851631 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237517397887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_47 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (4122924932647 / 5000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (139845089057 / 6250000000000 : ℝ))
      (E := (cell12817 ⟨47, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (4122924932647 / 5000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (139845089057 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_48 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (10303086730383 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118762708393 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨48, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (10303086730383 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118762708393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_49 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (41195456196641 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118764715079 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨49, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (41195456196641 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118764715079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_50 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (10294644284377 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (279691682821 / 12500000000000 : ℝ))
      (E := (cell12817 ⟨50, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (10294644284377 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (279691682821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_51 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82323419459831 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237537452327 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨51, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82323419459831 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237537452327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_52 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16457941583887 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237541455521 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨52, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16457941583887 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237541455521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_53 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20564004906419 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237545469057 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨53, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20564004906419 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237545469057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_54 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (5138897159409 / 6250000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237549489629 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨54, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (5138897159409 / 6250000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237549489629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_55 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (10273589083271 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237553513727 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨55, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (10273589083271 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237553513727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_56 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (5134693371551 / 6250000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (69923671203 / 3125000000000 : ℝ))
      (E := (cell12817 ⟨56, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (5134693371551 / 6250000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (69923671203 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_57 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16424299671779 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559390374563 / 25000000000000 : ℝ))
      (E := (cell12817 ⟨57, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16424299671779 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559390374563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_58 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82087925880949 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237565509751 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨58, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82087925880949 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237565509751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_59 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82054376483659 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559392377163 / 25000000000000 : ℝ))
      (E := (cell12817 ⟨59, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82054376483659 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559392377163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12818_40 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (20673946566513 / 25000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (447474871347 / 20000000000000 : ℝ))
      (E := (cell12818 ⟨40, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (20673946566513 / 25000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (447474871347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_41 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82661817421561 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237378382617 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨41, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82661817421561 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237378382617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_42 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41313936070437 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118691191647 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨42, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41313936070437 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118691191647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_43 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (8259395039439 / 10000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (279673302071 / 12500000000000 : ℝ))
      (E := (cell12818 ⟨43, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (8259395039439 / 10000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (279673302071 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_44 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41280026076327 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118695211207 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨44, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41280026076327 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118695211207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_45 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82526177386361 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237394399371 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨45, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82526177386361 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237394399371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_46 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41246163033177 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118699202331 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨46, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41246163033177 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118699202331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_47 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41229249081811 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (447480487293 / 20000000000000 : ℝ))
      (E := (cell12818 ⟨47, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41229249081811 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (447480487293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_48 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41212346824649 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237406433799 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨48, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41212346824649 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237406433799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_49 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41195456247331 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (447482090663 / 20000000000000 : ℝ))
      (E := (cell12818 ⟨49, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41195456247331 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (447482090663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_50 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (2573661083473 / 3125000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237414433557 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨50, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (2573661083473 / 3125000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237414433557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_51 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41161710075143 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (5593546077 / 250000000000 : ℝ))
      (E := (cell12818 ⟨51, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41161710075143 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (5593546077 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_52 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (4114485445191 / 5000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118711221079 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨52, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (4114485445191 / 5000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118711221079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_53 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82256020903589 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (279678308067 / 12500000000000 : ℝ))
      (E := (cell12818 ⟨53, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82256020903589 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (279678308067 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_54 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41111178060791 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237430494631 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨54, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41111178060791 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237430494631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_55 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82188714529929 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237434469819 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨55, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82188714529929 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237434469819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_56 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82155096100899 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237438504577 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨56, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82155096100899 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237438504577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_57 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82121500806899 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237442476731 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨57, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82121500806899 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237442476731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_58 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (3283517144819 / 4000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118723250219 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨58, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (3283517144819 / 4000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118723250219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_59 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41027189757153 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (89498020489 / 4000000000000 : ℝ))
      (E := (cell12818 ⟨59, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41027189757153 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (89498020489 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12819_40 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41347891848639 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237255404919 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨40, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41347891848639 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237255404919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_41 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82661815151167 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237259372743 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨41, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82661815151167 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237259372743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_42 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82627870168449 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118631716807 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨42, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82627870168449 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118631716807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_43 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82593948719523 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237267410157 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨43, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82593948719523 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237267410157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_44 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (16512010154987 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559317854691 / 25000000000000 : ℝ))
      (E := (cell12819 ⟨44, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (16512010154987 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559317854691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_45 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41263088152691 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237275399167 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨45, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41263088152691 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237275399167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_46 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41246162640853 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559319852147 / 25000000000000 : ℝ))
      (E := (cell12819 ⟨46, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41246162640853 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559319852147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_47 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (5153656104681 / 6250000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118641722603 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨47, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (5153656104681 / 6250000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118641722603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_48 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82424693456089 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237287448037 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨48, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82424693456089 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237287448037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_49 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82390912596563 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559322868433 / 25000000000000 : ℝ))
      (E := (cell12819 ⟨49, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82390912596563 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559322868433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_50 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82357155067741 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237295460837 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨50, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82357155067741 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237295460837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_51 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (10290427605149 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237299465621 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨51, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (10290427605149 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237299465621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_52 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41144854944311 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118651742601 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨52, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41144854944311 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118651742601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_53 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82256022181883 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (111865372871 / 5000000000000 : ℝ))
      (E := (cell12819 ⟨53, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82256022181883 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (111865372871 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_54 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41111178846483 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237311497073 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨54, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41111178846483 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237311497073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_55 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82188716394001 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118657741249 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨55, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82188716394001 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118657741249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_56 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41077549128629 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (223731952817 / 10000000000000 : ℝ))
      (E := (cell12819 ⟨56, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41077549128629 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (223731952817 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_57 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (10265187906893 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559330877979 / 25000000000000 : ℝ))
      (E := (cell12819 ⟨57, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (10265187906893 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559330877979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_58 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (16417586272041 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559331886973 / 25000000000000 : ℝ))
      (E := (cell12819 ⟨58, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (16417586272041 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559331886973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_59 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82054382545123 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118665756709 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨59, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82054382545123 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118665756709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12820_40 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (82695781129347 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237136450031 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨40, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (82695781129347 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237136450031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_41 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (4133090644079 / 5000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237140477399 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨41, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (4133090644079 / 5000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237140477399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_42 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (16525573639359 / 20000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (279643060117 / 12500000000000 : ℝ))
      (E := (cell12820 ⟨42, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (16525573639359 / 20000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (279643060117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_43 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (82593947045391 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (447429691923 / 20000000000000 : ℝ))
      (E := (cell12820 ⟨43, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (82593947045391 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (447429691923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_44 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (20640012349479 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118576235521 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨44, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (20640012349479 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118576235521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_45 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41263087612533 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237156454951 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨45, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41263087612533 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237156454951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_46 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (16498464899537 / 20000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237160468563 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨46, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (16498464899537 / 20000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237160468563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_47 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (20614624296691 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118582255027 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨47, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (20614624296691 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118582255027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_48 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (82424693263437 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559292129611 / 25000000000000 : ℝ))
      (E := (cell12820 ⟨48, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (82424693263437 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559292129611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_49 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41195456349493 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (139823280713 / 6250000000000 : ℝ))
      (E := (cell12820 ⟨49, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41195456349493 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (139823280713 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_50 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41178577732417 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223717648541 / 10000000000000 : ℝ))
      (E := (cell12820 ⟨50, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41178577732417 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223717648541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_51 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (82323421532549 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237180497773 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨51, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (82323421532549 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237180497773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_52 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (1028621385923 / 1250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237184525613 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨52, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (1028621385923 / 1250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237184525613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_53 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41128011730279 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223718850677 / 10000000000000 : ℝ))
      (E := (cell12820 ⟨53, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41128011730279 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223718850677 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_54 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (10277794908087 / 12500000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237192556041 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨54, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (10277794908087 / 12500000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237192556041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_55 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (5136794891149 / 6250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237196551761 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨55, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (5136794891149 / 6250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237196551761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_56 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (20538775103473 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237200549273 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨56, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (20538775103473 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237200549273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_57 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (82121505703629 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237204544647 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨57, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (82121505703629 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237204544647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_58 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41043967050071 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118604296463 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨58, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41043967050071 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118604296463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_59 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (5128399098507 / 6250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237212571431 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨59, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (5128399098507 / 6250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237212571431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12821_40 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41347889281129 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559254387709 / 25000000000000 : ℝ))
      (E := (cell12821 ⟨40, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41347889281129 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559254387709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_41 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82661810612799 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237021520243 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨41, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82661810612799 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237021520243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_42 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82627866225911 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118512762633 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨42, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82627866225911 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118512762633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_43 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41296972685997 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447405912989 / 20000000000000 : ℝ))
      (E := (cell12821 ⟨43, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41296972685997 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447405912989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_44 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (16512009604319 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237033520401 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨44, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (16512009604319 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237033520401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_45 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41263087072707 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (279629695841 / 12500000000000 : ℝ))
      (E := (cell12821 ⟨45, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41263087072707 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (279629695841 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_46 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82492323714293 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (223704158459 / 10000000000000 : ℝ))
      (E := (cell12821 ⟨46, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82492323714293 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (223704158459 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_47 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (10307312087403 / 12500000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559261393023 / 25000000000000 : ℝ))
      (E := (cell12821 ⟨47, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (10307312087403 / 12500000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559261393023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_48 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41212346535671 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (89481983443 / 4000000000000 : ℝ))
      (E := (cell12821 ⟨48, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41212346535671 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (89481983443 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_49 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (8239091280193 / 10000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559263391329 / 25000000000000 : ℝ))
      (E := (cell12821 ⟨49, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (8239091280193 / 10000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559263391329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_50 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (20589288965603 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (89482302651 / 4000000000000 : ℝ))
      (E := (cell12821 ⟨50, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (20589288965603 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (89482302651 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_51 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82323422224357 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559265396569 / 25000000000000 : ℝ))
      (E := (cell12821 ⟨51, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82323422224357 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559265396569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_52 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82289711859473 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447413124487 / 20000000000000 : ℝ))
      (E := (cell12821 ⟨52, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82289711859473 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447413124487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_53 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41128012369807 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237069612589 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨53, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41128012369807 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237069612589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_54 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82222360836771 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (44741472249 / 2000000000000 : ℝ))
      (E := (cell12821 ⟨54, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82222360836771 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (44741472249 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_55 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (20547180030769 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (279634702313 / 12500000000000 : ℝ))
      (E := (cell12821 ⟨55, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (20547180030769 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (279634702313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_56 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82155102570801 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (89483265081 / 4000000000000 : ℝ))
      (E := (cell12821 ⟨56, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82155102570801 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (89483265081 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_57 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (16424301630471 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447417126817 / 20000000000000 : ℝ))
      (E := (cell12821 ⟨57, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (16424301630471 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447417126817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_58 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82087936840283 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237089635547 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨58, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82087936840283 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237089635547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_59 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82054388607271 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2184661803 / 97656250000 : ℝ))
      (E := (cell12821 ⟨59, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82054388607271 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2184661803 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12822_40 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (8269577599601 / 10000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (89475945943 / 4000000000000 : ℝ))
      (E := (cell12822 ⟨40, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (8269577599601 / 10000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (89475945943 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_41 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (10332726043103 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (55922565471 / 2500000000000 : ℝ))
      (E := (cell12822 ⟨41, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (10332726043103 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (55922565471 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_42 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41313932127899 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118453312703 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨42, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41313932127899 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118453312703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_43 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (82593943699331 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118455333659 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨43, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (82593943699331 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118455333659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_44 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41280023322987 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (17475895973 / 781250000000 : ℝ))
      (E := (cell12822 ⟨44, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41280023322987 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (17475895973 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_45 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (3301046922657 / 4000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236918675621 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨45, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (3301046922657 / 4000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236918675621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_46 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (10311540366441 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236922697769 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨46, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (10311540366441 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236922697769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_47 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (20614624053069 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118463345121 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨47, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (20614624053069 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118463345121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_48 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (20606173219951 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118465354939 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨48, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (20606173219951 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118465354939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_49 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (20597728226349 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118467347727 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨49, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (20597728226349 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118467347727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_50 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (82357156260477 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236938703429 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨50, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (82357156260477 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236938703429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_51 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (16464684583323 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (223694273113 / 10000000000000 : ℝ))
      (E := (cell12822 ⟨51, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (16464684583323 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (223694273113 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_52 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41144856422761 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118473358313 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨52, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41144856422761 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118473358313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_53 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (1645120520381 / 2000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118475357907 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨53, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (1645120520381 / 2000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118475357907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_54 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (82222362409191 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236954725389 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨54, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (82222362409191 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236954725389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_55 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (1027359024851 / 1250000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (279619842729 / 12500000000000 : ℝ))
      (E := (cell12822 ⟨55, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (1027359024851 / 1250000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (279619842729 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_56 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41077552363993 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236962761423 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨56, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41077552363993 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236962761423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_57 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (82121510601321 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236966780229 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨57, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (82121510601321 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236966780229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_58 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (8208793958063 / 10000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (559242683733 / 25000000000000 : ℝ))
      (E := (cell12822 ⟨58, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (8208793958063 / 10000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (559242683733 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_59 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (410271958193 / 500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (559243699683 / 25000000000000 : ℝ))
      (E := (cell12822 ⟨59, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (410271958193 / 500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (559243699683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12823_40 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (20673943357651 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236779743247 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨40, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (20673943357651 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236779743247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_41 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (16532361215531 / 20000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236783773189 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨41, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (16532361215531 / 20000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236783773189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_42 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41313931143227 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236787781361 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨42, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41313931143227 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236787781361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_43 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82593942027403 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118395883367 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨43, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82593942027403 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118395883367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_44 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (20640011317763 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118397893457 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨44, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (20640011317763 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118397893457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_45 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82526171988099 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (223679978163 / 10000000000000 : ℝ))
      (E := (cell12823 ⟨45, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82526171988099 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (223679978163 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_46 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82492322149391 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236803808101 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨46, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82492322149391 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236803808101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_47 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (515365598287 / 625000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (111840390279 / 5000000000000 : ℝ))
      (E := (cell12823 ⟨47, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (515365598287 / 625000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (111840390279 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_48 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82424692688823 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118405915453 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨48, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82424692688823 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118405915453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_49 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (10298864126173 / 12500000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236815822853 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨49, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (10298864126173 / 12500000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236815822853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_50 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (20589289164757 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118409918941 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨50, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (20589289164757 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118409918941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_51 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (3292936944373 / 4000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236823814299 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨51, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (3292936944373 / 4000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236823814299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_52 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82289713831987 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236827867227 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨52, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82289713831987 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236827867227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_53 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41128013649433 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236831875509 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨53, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41128013649433 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236831875509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_54 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82222363981957 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236835835769 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨54, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82222363981957 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236835835769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_55 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82188723853393 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (27960498283 / 1250000000000 : ℝ))
      (E := (cell12823 ⟨55, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82188723853393 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (27960498283 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_56 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41077553442723 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (279605486667 / 12500000000000 : ℝ))
      (E := (cell12823 ⟨56, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41077553442723 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (279605486667 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_57 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41060756525263 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118423932383 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨57, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41060756525263 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118423932383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_58 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82087942321183 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559212972771 / 25000000000000 : ℝ))
      (E := (cell12823 ⟨58, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82087942321183 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559212972771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_59 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82054394670099 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118427954407 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨59, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82054394670099 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118427954407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12824_40 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (2067394271651 / 2500000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559165238093 / 25000000000000 : ℝ))
      (E := (cell12824 ⟨40, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (2067394271651 / 2500000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559165238093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_41 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82661803811291 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (223666492451 / 10000000000000 : ℝ))
      (E := (cell12824 ⟨41, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82661803811291 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (223666492451 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_42 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (2065696507947 / 2500000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559167233581 / 25000000000000 : ℝ))
      (E := (cell12824 ⟨42, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (2065696507947 / 2500000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559167233581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_43 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82593940356209 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (89466916881 / 4000000000000 : ℝ))
      (E := (cell12824 ⟨43, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82593940356209 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (89466916881 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_44 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82560043896827 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (111833847261 / 5000000000000 : ℝ))
      (E := (cell12824 ⟨44, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82560043896827 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (111833847261 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_45 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20631542727609 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118340471817 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨45, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20631542727609 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118340471817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_46 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82492321367881 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (279585621811 / 12500000000000 : ℝ))
      (E := (cell12824 ⟨46, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82492321367881 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (279585621811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_47 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20614623810039 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236688977033 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨47, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20614623810039 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236688977033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_48 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41212346249199 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559173252027 / 25000000000000 : ℝ))
      (E := (cell12824 ⟨48, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41212346249199 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559173252027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_49 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20597728278473 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236697006487 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨49, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20597728278473 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236697006487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_50 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (5147322316129 / 6250000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447340193927 / 20000000000000 : ℝ))
      (E := (cell12824 ⟨50, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (5147322316129 / 6250000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447340193927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_51 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (16464684860497 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236705012839 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨51, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (16464684860497 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236705012839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_52 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41144857409433 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2795886269 / 125000000000 : ℝ))
      (E := (cell12824 ⟨52, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41144857409433 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2795886269 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_53 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41128014289531 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236713032613 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨53, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41128014289531 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236713032613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_54 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20555591388767 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (55917925067 / 2500000000000 : ℝ))
      (E := (cell12824 ⟨54, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20555591388767 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (55917925067 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_55 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (10273590714877 / 12500000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118360520019 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨55, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (10273590714877 / 12500000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118360520019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_56 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (4107755452159 / 5000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559181255691 / 25000000000000 : ℝ))
      (E := (cell12824 ⟨56, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (4107755452159 / 5000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559181255691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_57 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20530378874993 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (223672906517 / 10000000000000 : ℝ))
      (E := (cell12824 ⟨57, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20530378874993 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (223672906517 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_58 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (4104397253097 / 5000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (279591630603 / 12500000000000 : ℝ))
      (E := (cell12824 ⟨58, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (4104397253097 / 5000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (279591630603 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_59 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82054397701769 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236737075723 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨59, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82054397701769 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236737075723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

end BstLean.Part268
