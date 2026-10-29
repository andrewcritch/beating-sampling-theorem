import BstLean.Part268CellShard32Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13150_0 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (5254338469753 / 6250000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (87964618651 / 4000000000000 : ℝ))
      (E := (cell13150 ⟨0, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (5254338469753 / 6250000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (87964618651 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_1 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (84034527000901 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199119459913 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨1, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (84034527000901 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199119459913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_2 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (3359986531937 / 4000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099561728879 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨2, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (3359986531937 / 4000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099561728879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_3 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (20991206093097 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439825493637 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨3, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (20991206093097 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439825493637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_4 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83930010186749 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199131499309 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨4, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83930010186749 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199131499309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_5 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (10486902588207 / 12500000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (68722984407 / 3125000000000 : ℝ))
      (E := (cell13150 ⟨5, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (10486902588207 / 12500000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (68722984407 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_6 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (20965113973361 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199139538861 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨6, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (20965113973361 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199139538861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_7 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (20956428928659 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099571752069 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨7, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (20956428928659 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099571752069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_8 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83791000133939 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199147519901 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨8, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83791000133939 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199147519901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_9 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83756309116247 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439830306987 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨9, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83756309116247 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439830306987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_10 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41860821313317 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549788888943 / 25000000000000 : ℝ))
      (E := (cell13150 ⟨10, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41860821313317 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549788888943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_11 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41843500315179 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099579794347 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨11, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41843500315179 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099579794347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_12 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41826191546429 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099581790801 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨12, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41826191546429 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099581790801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_13 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83617789979751 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549791899593 / 25000000000000 : ℝ))
      (E := (cell13150 ⟨13, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83617789979751 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549791899593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_14 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41791610628417 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439834328909 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨14, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41791610628417 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439834328909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_15 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83548676890079 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199175667219 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨15, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83548676890079 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199175667219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_16 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83514156845637 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199179671377 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨16, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83514156845637 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199179671377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_17 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (83479661089833 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199183661763 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨17, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (83479661089833 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199183661763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_18 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (16689037917833 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199187701153 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨18, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (16689037917833 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199187701153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_19 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41705371155153 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199191677283 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨19, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41705371155153 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199191677283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13151_0 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (84069401406853 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549751111599 / 25000000000000 : ℝ))
      (E := (cell13151 ⟨0, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (84069401406853 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549751111599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_1 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (8403451289797 / 10000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099504247067 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨1, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (8403451289797 / 10000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099504247067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_2 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83999649201751 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099506244137 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨2, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83999649201751 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099506244137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_3 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83964810281967 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (6871926547 / 312500000000 : ℝ))
      (E := (cell13151 ⟨3, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83964810281967 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (6871926547 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_4 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (3357199844103 / 4000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199020522553 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨4, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (3357199844103 / 4000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199020522553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_5 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41947603313861 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (4294969767 / 195312500000 : ℝ))
      (E := (cell13151 ⟨5, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41947603313861 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (4294969767 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_6 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41930220910873 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099514277511 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨6, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41930220910873 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099514277511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_7 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83825701649167 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199032574847 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨7, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83825701649167 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199032574847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_8 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (16758197214939 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (274879573401 / 12500000000000 : ℝ))
      (E := (cell13151 ⟨8, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (16758197214939 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (274879573401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_9 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41878147531611 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (274880074861 / 12500000000000 : ℝ))
      (E := (cell13151 ⟨9, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41878147531611 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (274880074861 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_10 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41860814289911 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099522308209 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨10, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41860814289911 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099522308209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_11 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (16737397317951 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199048587969 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨11, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (16737397317951 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199048587969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_12 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83652369058457 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099526317887 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨12, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83652369058457 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099526317887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_13 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83617775951547 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199056649377 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨13, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83617775951547 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199056649377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_14 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (4179160361741 / 5000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199060634251 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨14, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (4179160361741 / 5000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199060634251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_15 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (20887165718563 / 25000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549766163457 / 25000000000000 : ℝ))
      (E := (cell13151 ⟨15, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (20887165718563 / 25000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549766163457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_16 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83514142835991 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (274883581867 / 12500000000000 : ℝ))
      (E := (cell13151 ⟨16, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83514142835991 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (274883581867 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_17 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41739823543181 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (219907270057 / 10000000000000 : ℝ))
      (E := (cell13151 ⟨17, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41739823543181 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (219907270057 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_18 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (10430646948983 / 12500000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199076678753 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨18, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (10430646948983 / 12500000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199076678753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_19 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (83410728319169 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (17180318049 / 781250000000 : ℝ))
      (E := (cell13151 ⟨19, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (83410728319169 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (17180318049 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13152_0 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (42034693649903 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198893480147 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨0, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (42034693649903 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198893480147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_1 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (16806899759437 / 20000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198897524133 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨1, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (16806899759437 / 20000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198897524133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_2 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (10499954388403 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198901514567 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨2, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (10499954388403 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198901514567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_3 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83964796193691 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (549726379419 / 25000000000000 : ℝ))
      (E := (cell13152 ⟨3, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83964796193691 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (549726379419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_4 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (16785996404109 / 20000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198909541577 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨4, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (16785996404109 / 20000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198909541577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_5 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (20973798137983 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (549728384041 / 25000000000000 : ℝ))
      (E := (cell13152 ⟨5, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (20973798137983 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (549728384041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_6 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (8386042775219 / 10000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (439783513393 / 20000000000000 : ℝ))
      (E := (cell13152 ⟨6, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (8386042775219 / 10000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (439783513393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_7 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83825687585841 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198921583319 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨7, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83825687585841 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198921583319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_8 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (10473871502199 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099462796129 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨8, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (10473871502199 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099462796129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_9 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (5234767563271 / 6250000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099464800281 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨9, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (5234767563271 / 6250000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099464800281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_10 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83721614535149 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099466807381 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨10, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83721614535149 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099466807381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_11 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (10460871568911 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198937641141 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨11, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (10460871568911 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198937641141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_12 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (5228272189137 / 6250000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (5497354069 / 250000000000 : ℝ))
      (E := (cell13152 ⟨12, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (5228272189137 / 6250000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (5497354069 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_13 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41808880962739 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198945638013 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨13, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41808880962739 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198945638013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_14 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41791596607471 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099474838963 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨14, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41791596607471 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099474838963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_15 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83548648860559 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (219895369443 / 10000000000000 : ℝ))
      (E := (cell13152 ⟨15, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83548648860559 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (219895369443 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_16 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83514128828477 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099478846257 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨16, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83514128828477 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099478846257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_17 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (83479633085023 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (4294847139 / 195312500000 : ℝ))
      (E := (cell13152 ⟨17, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (83479633085023 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (4294847139 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_18 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41722580798347 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198965710419 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨18, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41722580798347 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198965710419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_19 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41705357165081 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198969739053 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨19, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41705357165081 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2198969739053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13153_0 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (84069373194907 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274847820941 / 12500000000000 : ℝ))
      (E := (cell13153 ⟨0, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (84069373194907 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274847820941 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_1 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (21008621174637 / 25000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198786549909 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨1, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (21008621174637 / 25000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198786549909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_2 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83999621014843 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198790594539 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨2, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83999621014843 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198790594539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_3 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (2099119552689 / 2500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099397297007 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨3, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (2099119552689 / 2500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099397297007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_4 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41964983970329 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198798614329 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨4, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41964983970329 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198798614329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_5 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16779035695657 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (17590420843 / 800000000000 : ℝ))
      (E := (cell13153 ⟨5, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16779035695657 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (17590420843 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_6 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83860413684777 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549701658171 / 25000000000000 : ℝ))
      (E := (cell13153 ⟨6, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83860413684777 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549701658171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_7 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16765134704931 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274851330699 / 12500000000000 : ℝ))
      (E := (cell13153 ⟨7, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16765134704931 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274851330699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_8 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83790957962629 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549703662783 / 25000000000000 : ℝ))
      (E := (cell13153 ⟨8, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83790957962629 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549703662783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_9 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (8375626696359 / 10000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549704664021 / 25000000000000 : ℝ))
      (E := (cell13153 ⟨9, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (8375626696359 / 10000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549704664021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_10 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16744320098523 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099411333489 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨10, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16744320098523 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099411333489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_11 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (1046086981437 / 1250000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198826690099 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨11, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (1046086981437 / 1250000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198826690099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_12 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (2614135656127 / 3125000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (54970768287 / 2500000000000 : ℝ))
      (E := (cell13153 ⟨12, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (2614135656127 / 3125000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (54970768287 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_13 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (10452218487693 / 12500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099417369377 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨13, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (10452218487693 / 12500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099417369377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_14 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41791589598599 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (219883871739 / 10000000000000 : ℝ))
      (E := (cell13153 ⟨14, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41791589598599 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (219883871739 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_15 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (83548634848999 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274855341353 / 12500000000000 : ℝ))
      (E := (cell13153 ⟨15, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (83548634848999 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274855341353 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_16 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (10439264352887 / 12500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (219884678411 / 10000000000000 : ℝ))
      (E := (cell13153 ⟨16, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (10439264352887 / 12500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (219884678411 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_17 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16695923817163 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198850765559 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨17, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16695923817163 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198850765559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_18 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41722573801827 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198854796153 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨18, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41722573801827 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198854796153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_19 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16682140068657 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099429410963 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨19, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16682140068657 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099429410963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13154_0 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (16813871818431 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198671650687 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨0, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (16813871818431 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198671650687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_1 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (84034470602057 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (109933781467 / 5000000000000 : ℝ))
      (E := (cell13154 ⟨1, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (84034470602057 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (109933781467 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_2 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83999606924607 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (219867967029 / 10000000000000 : ℝ))
      (E := (cell13154 ⟨2, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83999606924607 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (219867967029 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_3 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83964768023573 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198683666133 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨3, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83964768023573 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198683666133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_4 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (16785990772583 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099343841431 / 50000000000000 : ℝ))
      (E := (cell13154 ⟨4, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (16785990772583 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099343841431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_5 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83895164406781 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (68709114699 / 3125000000000 : ℝ))
      (E := (cell13154 ⟨5, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83895164406781 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (68709114699 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_6 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (16772079923901 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439739138837 / 20000000000000 : ℝ))
      (E := (cell13154 ⟨6, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (16772079923901 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439739138837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_7 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (8382565946561 / 10000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198699703649 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨7, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (8382565946561 / 10000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198699703649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_8 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (16758188781961 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198703763831 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨8, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (16758188781961 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198703763831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_9 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83756252916983 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439741553091 / 20000000000000 : ℝ))
      (E := (cell13154 ⟨9, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83756252916983 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439741553091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_10 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (41860793226109 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198711773069 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨10, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (41860793226109 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198711773069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_11 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (163451063439 / 195312500000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439743158591 / 20000000000000 : ℝ))
      (E := (cell13154 ⟨11, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (163451063439 / 195312500000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439743158591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_12 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83652326968071 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274839971627 / 12500000000000 : ℝ))
      (E := (cell13154 ⟨12, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83652326968071 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274839971627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_13 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (41808866939873 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549680944281 / 25000000000000 : ℝ))
      (E := (cell13154 ⟨13, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (41808866939873 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549680944281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_14 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83583165181589 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274840976353 / 12500000000000 : ℝ))
      (E := (cell13154 ⟨14, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83583165181589 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274840976353 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_15 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (20887155209893 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549682955303 / 25000000000000 : ℝ))
      (E := (cell13154 ⟨15, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (20887155209893 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549682955303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_16 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (10439262602481 / 12500000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198735871497 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨16, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (10439262602481 / 12500000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198735871497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_17 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (83479605088739 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274842481249 / 12500000000000 : ℝ))
      (E := (cell13154 ⟨17, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (83479605088739 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274842481249 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_18 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (16689026722549 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (27484298471 / 1250000000000 : ℝ))
      (E := (cell13154 ⟨18, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (16689026722549 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (27484298471 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_19 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (41705343179269 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (137421743787 / 6250000000000 : ℝ))
      (E := (cell13154 ⟨19, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (41705343179269 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (137421743787 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13155_0 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (1681386899831 / 2000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (274820091203 / 12500000000000 : ℝ))
      (E := (cell13155 ⟨0, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (1681386899831 / 2000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (274820091203 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_1 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (84034456507711 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198564762429 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨1, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (84034456507711 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198564762429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_2 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (16799918567303 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198568741823 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨2, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (16799918567303 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198568741823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_3 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (83964753941731 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549643197989 / 25000000000000 : ℝ))
      (E := (cell13155 ⟨3, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (83964753941731 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549643197989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_4 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (20982484946829 / 25000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198576805123 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨4, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (20982484946829 / 25000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198576805123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_5 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41947575168709 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549645197279 / 25000000000000 : ℝ))
      (E := (cell13155 ⟨5, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41947575168709 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549645197279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_6 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41930192778187 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439716961893 / 20000000000000 : ℝ))
      (E := (cell13155 ⟨6, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41930192778187 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439716961893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_7 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (16765129081741 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549647203877 / 25000000000000 : ℝ))
      (E := (cell13155 ⟨7, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (16765129081741 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549647203877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_8 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (83790929859121 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (87943712571 / 4000000000000 : ℝ))
      (E := (cell13155 ⟨8, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (83790929859121 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (87943712571 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_9 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (83756238872513 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099298435307 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨9, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (83756238872513 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099298435307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_10 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41860786206979 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198600874947 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨10, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41860786206979 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198600874947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_11 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (10460866306089 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198604891601 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨11, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (10460866306089 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198604891601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_12 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41826156471107 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099304434237 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨12, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41826156471107 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099304434237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_13 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41808859930041 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198612927601 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨13, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41808859930041 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198612927601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_14 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (5223946948007 / 6250000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198616900051 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨14, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (5223946948007 / 6250000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198616900051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_15 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41774303416139 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198620907391 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨15, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41774303416139 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198620907391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_16 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (8351408681873 / 10000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099312477339 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨16, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (8351408681873 / 10000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099312477339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_17 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (83479591093793 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (109931446511 / 5000000000000 : ℝ))
      (E := (cell13155 ⟨17, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (83479591093793 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (109931446511 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_18 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (16689023924793 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198632955001 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨18, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (16689023924793 / 20000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198632955001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_19 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (83410672375919 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099318487527 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨19, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (83410672375919 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099318487527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13156_0 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (84069330893091 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439689972439 / 20000000000000 : ℝ))
      (E := (cell13156 ⟨0, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (84069330893091 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439689972439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_1 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (84034442415511 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099226945649 / 50000000000000 : ℝ))
      (E := (cell13156 ⟨1, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (84034442415511 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099226945649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_2 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83999578750569 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549614466759 / 25000000000000 : ℝ))
      (E := (cell13156 ⟨2, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83999578750569 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549614466759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_3 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83964739862031 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198461913563 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨3, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83964739862031 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198461913563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_4 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41964962856929 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198465923169 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨4, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41964962856929 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198465923169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_5 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83895136270197 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (68702184489 / 3125000000000 : ℝ))
      (E := (cell13156 ⟨5, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83895136270197 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (68702184489 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_6 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83860371495383 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219847392053 / 10000000000000 : ℝ))
      (E := (cell13156 ⟨6, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83860371495383 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219847392053 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_7 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (4191281567697 / 5000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198477923153 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨7, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (4191281567697 / 5000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198477923153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_8 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (5236932238161 / 6250000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549620494147 / 25000000000000 : ℝ))
      (E := (cell13156 ⟨8, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (5236932238161 / 6250000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549620494147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_9 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41878112415091 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198485971559 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨9, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41878112415091 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198485971559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_10 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (16744311675567 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099244986307 / 50000000000000 : ℝ))
      (E := (cell13156 ⟨10, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (16744311675567 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099244986307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_11 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (10460864552349 / 12500000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439698797207 / 20000000000000 : ℝ))
      (E := (cell13156 ⟨11, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (10460864552349 / 12500000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439698797207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_12 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (20913074729623 / 25000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198498017857 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨12, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (20913074729623 / 25000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198498017857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_13 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (10452213230319 / 12500000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219850201571 / 10000000000000 : ℝ))
      (E := (cell13156 ⟨13, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (10452213230319 / 12500000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219850201571 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_14 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83583137156769 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (8794024173 / 400000000000 : ℝ))
      (E := (cell13156 ⟨14, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83583137156769 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (8794024173 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_15 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83548592827117 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (137406877973 / 6250000000000 : ℝ))
      (E := (cell13156 ⟨15, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83548592827117 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (137406877973 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_16 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (2609814775617 / 3125000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (54962852297 / 2500000000000 : ℝ))
      (E := (cell13156 ⟨16, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (2609814775617 / 3125000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (54962852297 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_17 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41739788550489 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198518064493 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨17, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41739788550489 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198518064493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_18 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (16689021127463 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198522086393 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨18, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (16689021127463 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198522086393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_19 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (83410658395429 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219852610361 / 10000000000000 : ℝ))
      (E := (cell13156 ⟨19, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (83410658395429 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219852610361 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13157_0 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (42034658398389 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198338990547 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨0, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (42034658398389 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198338990547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_1 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (5252151770341 / 6250000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198343015949 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨1, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (5252151770341 / 6250000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198343015949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_2 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41999782333383 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198346988033 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨2, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41999782333383 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198346988033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_3 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (3358589031379 / 4000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274793878869 / 12500000000000 : ℝ))
      (E := (cell13157 ⟨3, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (3358589031379 / 4000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274793878869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_4 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (83929911642543 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198355036999 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨4, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (83929911642543 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198355036999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_5 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (83895122205117 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (34349360499 / 1562500000000 : ℝ))
      (E := (cell13157 ⟨5, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (83895122205117 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (34349360499 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_6 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (83860357436533 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (17586904683 / 800000000000 : ℝ))
      (E := (cell13157 ⟨6, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (83860357436533 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (17586904683 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_7 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41912808650657 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099183542301 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨7, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41912808650657 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099183542301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_8 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (10473862720521 / 12500000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274796384581 / 12500000000000 : ℝ))
      (E := (cell13157 ⟨8, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (10473862720521 / 12500000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274796384581 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_9 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (20939052697497 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099187563179 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨9, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (20939052697497 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099187563179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_10 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (10465193042981 / 12500000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099189562079 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨10, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (10465193042981 / 12500000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099189562079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_11 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (2615215699719 / 3125000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (219838313437 / 10000000000000 : ℝ))
      (E := (cell13157 ⟨11, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (2615215699719 / 3125000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (219838313437 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_12 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (10456535612113 / 12500000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274798395379 / 12500000000000 : ℝ))
      (E := (cell13157 ⟨12, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (10456535612113 / 12500000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274798395379 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_13 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (20904422956789 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (219839115777 / 10000000000000 : ℝ))
      (E := (cell13157 ⟨13, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (20904422956789 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (219839115777 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_14 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41791561573779 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099197591121 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨14, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41791561573779 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099197591121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_15 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41774289412043 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (109919959177 / 5000000000000 : ℝ))
      (E := (cell13157 ⟨15, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41774289412043 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (109919959177 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_16 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (83514058822889 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (549600806219 / 25000000000000 : ℝ))
      (E := (cell13157 ⟨16, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (83514058822889 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (549600806219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_17 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (20869890777573 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198407194563 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨17, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (20869890777573 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198407194563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_18 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41722545826397 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198411213581 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨18, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41722545826397 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198411213581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_19 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41705322208533 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (549603806991 / 25000000000000 : ℝ))
      (E := (cell13157 ⟨19, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41705322208533 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (549603806991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13158_0 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (8406930270261 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439645634507 / 20000000000000 : ℝ))
      (E := (cell13158 ⟨0, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (8406930270261 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439645634507 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_1 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (16806882847509 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198232136383 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨1, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (16806882847509 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198232136383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_2 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (41999775292553 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099118081357 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨2, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (41999775292553 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099118081357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_3 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83964711709061 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198240202051 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨3, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83964711709061 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198240202051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_4 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83929897573369 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099122102281 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨4, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83929897573369 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099122102281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_5 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (41947554071089 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198248236009 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨5, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (41947554071089 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198248236009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_6 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83860343379823 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198252246007 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨6, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83860343379823 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198252246007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_7 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83825603250827 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198256241839 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨7, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83825603250827 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198256241839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_8 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83790887719899 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198260230537 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨8, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83790887719899 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198260230537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_9 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (8375619675193 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198264276947 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨9, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (8375619675193 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198264276947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_10 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (41860765155999 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (549567067873 / 25000000000000 : ℝ))
      (E := (cell13158 ⟨10, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (41860765155999 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (549567067873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_11 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (41843444182679 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099136139249 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨11, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (41843444182679 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099136139249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_12 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (1673045417549 / 2000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198276303999 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨12, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (1673045417549 / 2000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198276303999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_13 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (20904419453473 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (274785036953 / 12500000000000 : ℝ))
      (E := (cell13158 ⟨13, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (20904419453473 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (274785036953 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_14 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (4081206501 / 4882812500 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (549571079257 / 25000000000000 : ℝ))
      (E := (cell13158 ⟨14, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (4081206501 / 4882812500 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (549571079257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_15 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83548564823187 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (219828837351 / 10000000000000 : ℝ))
      (E := (cell13158 ⟨15, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83548564823187 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (219828837351 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_16 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (20878511207041 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198292353669 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨16, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (20878511207041 / 25000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198292353669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_17 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (16695909824347 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198296378681 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨17, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (16695909824347 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198296378681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_18 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83445077670401 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198300394841 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨18, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83445077670401 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198300394841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_19 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (83410630440831 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439660881283 / 20000000000000 : ℝ))
      (E := (cell13158 ⟨19, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (83410630440831 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439660881283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13159_0 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (84069288610587 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099058675153 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨0, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (84069288610587 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099058675153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_1 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (42017200075889 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (439624273671 / 20000000000000 : ℝ))
      (E := (cell13159 ⟨1, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (42017200075889 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (439624273671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_2 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (8399953650559 / 10000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (109906266659 / 5000000000000 : ℝ))
      (E := (cell13159 ⟨2, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (8399953650559 / 10000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (109906266659 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_3 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83964697635789 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (439625873787 / 20000000000000 : ℝ))
      (E := (cell13159 ⟨3, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83964697635789 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (439625873787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_4 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (2622808859573 / 3125000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198133367911 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨4, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (2622808859573 / 3125000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198133367911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_5 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41947547040689 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198137395871 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨5, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41947547040689 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198137395871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_6 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83860329325251 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549535350607 / 25000000000000 : ℝ))
      (E := (cell13159 ⟨6, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83860329325251 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549535350607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_7 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41912794601239 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099072697433 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨7, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41912794601239 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099072697433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_8 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41895436838883 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198149438259 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨8, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41895436838883 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198149438259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_9 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83756182716009 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099076711663 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨9, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83756182716009 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099076711663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_10 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41860758141141 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198157472707 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨10, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41860758141141 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198157472707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_11 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83686874341843 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198161476529 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨11, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83686874341843 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198161476529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_12 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (8365225686013 / 10000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099082749447 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨12, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (8365225686013 / 10000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099082749447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_13 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83617663802761 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (219816948743 / 10000000000000 : ℝ))
      (E := (cell13159 ⟨13, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83617663802761 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (219816948743 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_14 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (83583095135533 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198173505791 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨14, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (83583095135533 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198173505791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_15 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41774275412209 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198177501073 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨15, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41774275412209 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198177501073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_16 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (5219626927223 / 6250000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (274772692061 / 12500000000000 : ℝ))
      (E := (cell13159 ⟨16, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (5219626927223 / 6250000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (274772692061 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_17 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (20869883783827 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549546389649 / 25000000000000 : ℝ))
      (E := (cell13159 ⟨17, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (20869883783827 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549546389649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_18 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (16689012738027 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099094785951 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨18, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (16689012738027 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099094785951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_19 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41705308233361 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099096790333 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨19, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41705308233361 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099096790333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13160_0 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (84069274520709 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (109900326193 / 5000000000000 : ℝ))
      (E := (cell13160 ⟨0, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (84069274520709 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (109900326193 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_1 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (16806877213631 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099005269117 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨1, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (16806877213631 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099005269117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_2 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (16799904485643 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198014557333 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨2, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (16799904485643 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198014557333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_3 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (83964683564659 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (219801858953 / 10000000000000 : ℝ))
      (E := (cell13160 ⟨3, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (83964683564659 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (219801858953 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_4 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (20982467360361 / 25000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (439604516999 / 20000000000000 : ℝ))
      (E := (cell13160 ⟨4, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (20982467360361 / 25000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (439604516999 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_5 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41947540011359 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549506652373 / 25000000000000 : ℝ))
      (E := (cell13160 ⟨5, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41947540011359 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549506652373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_6 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41930157636409 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198030612633 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨6, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41930157636409 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198030612633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_7 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41912787578133 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198034601701 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨7, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41912787578133 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198034601701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_8 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (83790859637771 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (219803864177 / 10000000000000 : ℝ))
      (E := (cell13160 ⟨8, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (83790859637771 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (219803864177 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_9 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (5234760542639 / 6250000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099021311781 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨9, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (5234760542639 / 6250000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099021311781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_10 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41860751127351 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198046669713 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨10, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41860751127351 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198046669713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_11 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41843430160231 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099025335177 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨11, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41843430160231 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099025335177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_12 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (83652242844943 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198054689583 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨12, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (83652242844943 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198054689583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_13 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41808824896881 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198058675031 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨13, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41808824896881 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198058675031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_14 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (83583081132717 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (43961253807 / 2000000000000 : ℝ))
      (E := (cell13160 ⟨14, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (83583081132717 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (43961253807 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_15 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (4177426841389 / 5000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099033370421 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨15, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (4177426841389 / 5000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099033370421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_16 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41757008422551 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198070715103 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨16, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41757008422551 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198070715103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_17 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (2608735035969 / 3125000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198074734311 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨17, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (2608735035969 / 3125000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198074734311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_18 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (83445049711997 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198078744761 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨18, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (83445049711997 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198078744761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_19 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (4170530124737 / 5000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (274760351127 / 12500000000000 : ℝ))
      (E := (cell13160 ⟨19, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (4170530124737 / 5000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (274760351127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13161_0 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (42034630216487 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098947875527 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨0, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (42034630216487 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098947875527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_1 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (42017185993337 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197899761777 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨1, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (42017185993337 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197899761777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_2 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83999508352983 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274737972159 / 12500000000000 : ℝ))
      (E := (cell13161 ⟨2, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83999508352983 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274737972159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_3 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83964669495669 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274738475739 / 12500000000000 : ℝ))
      (E := (cell13161 ⟨3, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83964669495669 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274738475739 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_4 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (20982463844673 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197911797867 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨4, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (20982463844673 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197911797867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_5 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41947532983099 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197915818901 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨5, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41947532983099 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197915818901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_6 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (20965075305631 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098959909313 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨6, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (20965075305631 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098959909313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_7 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (654887196189 / 781250000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274740482793 / 12500000000000 : ℝ))
      (E := (cell13161 ⟨7, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (654887196189 / 781250000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274740482793 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_8 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83790845599911 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098963920537 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨8, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83790845599911 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098963920537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_9 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41878077325287 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439586375531 / 20000000000000 : ℝ))
      (E := (cell13161 ⟨9, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41878077325287 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439586375531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_10 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (10465186028657 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197935862513 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨10, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (10465186028657 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197935862513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_11 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41843423150607 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439587983617 / 20000000000000 : ℝ))
      (E := (cell13161 ⟨11, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41843423150607 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439587983617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_12 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (5228264301993 / 6250000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098971967101 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨12, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (5228264301993 / 6250000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098971967101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_13 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (16723527157379 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439589583317 / 20000000000000 : ℝ))
      (E := (cell13161 ⟨13, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (16723527157379 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439589583317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_14 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83583067132031 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274743991111 / 12500000000000 : ℝ))
      (E := (cell13161 ⟨14, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83583067132031 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (274743991111 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_15 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83548522833271 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197955976409 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨15, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83548522833271 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197955976409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_16 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (16702800571353 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098979973873 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨16, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (16702800571353 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1098979973873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_17 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (83479507168837 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (549490991019 / 25000000000000 : ℝ))
      (E := (cell13161 ⟨17, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (83479507168837 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (549490991019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_18 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41722517867993 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (137372998231 / 6250000000000 : ℝ))
      (E := (cell13161 ⟨18, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41722517867993 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (137372998231 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_19 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (20852647131221 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197972033167 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨19, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (20852647131221 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2197972033167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13162_0 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (84069246347383 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098892487017 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨0, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (84069246347383 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098892487017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_1 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (10504294738417 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197788981107 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨1, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (10504294738417 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197788981107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_2 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20999873569973 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197792992999 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨2, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20999873569973 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197792992999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_3 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83964655428821 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197797018083 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨3, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83964655428821 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197797018083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_4 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83929841318079 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098900532239 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨4, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83929841318079 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098900532239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_5 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (10486881488977 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098902512051 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨5, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (10486881488977 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098902512051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_6 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83860287174367 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098904539203 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨6, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83860287174367 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098904539203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_7 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (16765109414051 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197813060761 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨7, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (16765109414051 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197813060761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_8 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20947707891047 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (549454273553 / 25000000000000 : ℝ))
      (E := (cell13162 ⟨8, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20947707891047 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (549454273553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_9 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83756140621059 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197821127543 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨9, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83756140621059 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197821127543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_10 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83721474205943 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098912554599 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨10, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83721474205943 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098912554599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_11 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83686832284099 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (4395658207 / 200000000000 : ℝ))
      (E := (cell13162 ⟨11, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83686832284099 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (4395658207 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_12 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (16730442964193 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197833174619 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨12, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (16730442964193 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197833174619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_13 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (41808810891079 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197837153939 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨13, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (41808810891079 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197837153939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_14 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20895763283369 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (87913646529 / 4000000000000 : ℝ))
      (E := (cell13162 ⟨14, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20895763283369 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (87913646529 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_15 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83548508840891 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (68682662743 / 3125000000000 : ℝ))
      (E := (cell13162 ⟨15, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83548508840891 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (68682662743 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_16 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (16702797774111 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (219784917619 / 10000000000000 : ℝ))
      (E := (cell13162 ⟨16, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (16702797774111 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (219784917619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_17 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (10434936648599 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197853189643 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨17, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (10434936648599 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197853189643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_18 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (83445021762101 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197857252709 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨18, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (83445021762101 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197857252709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_19 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (41705287278577 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (26829361 / 1220703125 : ℝ))
      (E := (cell13162 ⟨19, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (41705287278577 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (26829361 / 1220703125 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13163_0 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (42034616131967 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (439534850131 / 20000000000000 : ℝ))
      (E := (cell13163 ⟨0, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (42034616131967 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (439534850131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_1 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (4201717191507 / 5000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197678254101 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨1, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (4201717191507 / 5000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197678254101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_2 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83999480208943 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098841131207 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨2, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83999480208943 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098841131207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_3 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (5247790085257 / 6250000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197686283967 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨3, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (5247790085257 / 6250000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197686283967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_4 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (16785965451921 / 20000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098845163439 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨4, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (16785965451921 / 20000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098845163439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_5 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (20973759464893 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (274711785383 / 12500000000000 : ℝ))
      (E := (cell13163 ⟨5, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (20973759464893 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (274711785383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_6 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83860273128347 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098849166989 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨6, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83860273128347 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098849166989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_7 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83825533030453 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (219770231299 / 10000000000000 : ℝ))
      (E := (cell13163 ⟨7, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83825533030453 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (219770231299 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_8 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83790817530599 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197706343143 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨8, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83790817530599 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197706343143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_9 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41878063296839 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (274713796653 / 12500000000000 : ℝ))
      (E := (cell13163 ⟨9, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41878063296839 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (274713796653 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_10 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (20930365046191 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (549428587919 / 25000000000000 : ℝ))
      (E := (cell13163 ⟨10, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (20930365046191 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (549428587919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_11 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83686818269117 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098859200467 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨11, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83686818269117 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098859200467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_12 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83652200812173 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197722410833 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨12, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83652200812173 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197722410833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_13 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (2613050243111 / 3125000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (34339475707 / 1562500000000 : ℝ))
      (E := (cell13163 ⟨13, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (2613050243111 / 3125000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (34339475707 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_14 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (1671660782741 / 2000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098865225771 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨14, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (1671660782741 / 2000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098865225771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_15 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (83548494850641 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197734434941 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨15, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (83548494850641 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197734434941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_16 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41756987443237 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197738458661 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨16, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41756987443237 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197738458661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_17 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41739739605437 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197742469263 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨17, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41739739605437 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197742469263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_18 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41722503895171 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197746471247 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨18, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41722503895171 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197746471247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_19 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (20852640147887 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (274718815897 / 12500000000000 : ℝ))
      (E := (cell13163 ⟨19, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (20852640147887 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (274718815897 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13164_0 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (21017304545657 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (274695440383 / 12500000000000 : ℝ))
      (E := (cell13164 ⟨0, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (21017304545657 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (274695440383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_1 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (16806865951017 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098783761443 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨1, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (16806865951017 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098783761443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_2 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83999466140133 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098785763811 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨2, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83999466140133 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098785763811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_3 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41982313650771 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (549393886411 / 25000000000000 : ℝ))
      (E := (cell13164 ⟨3, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41982313650771 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (549393886411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_4 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (8392981320327 / 10000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (219757958507 / 10000000000000 : ℝ))
      (E := (cell13164 ⟨4, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (8392981320327 / 10000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (219757958507 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_5 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (16779004761893 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197583595791 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨5, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (16779004761893 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197583595791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_6 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (5241266192779 / 6250000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197587585343 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨6, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (5241266192779 / 6250000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197587585343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_7 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20956379748197 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (219759161903 / 10000000000000 : ℝ))
      (E := (cell13164 ⟨7, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20956379748197 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (219759161903 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_8 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41895401749573 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197595645911 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨8, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41895401749573 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197595645911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_9 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83756112568431 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197599672767 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨9, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83756112568431 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197599672767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_10 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41860723082859 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197603648041 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨10, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41860723082859 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197603648041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_11 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41843402128133 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197607694167 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨11, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41843402128133 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197607694167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_12 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83652186805513 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (109880585049 / 5000000000000 : ℝ))
      (E := (cell13164 ⟨12, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83652186805513 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (109880585049 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_13 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83617593779077 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098807837099 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨13, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83617593779077 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098807837099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_14 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41791512571377 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197619735659 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨14, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41791512571377 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197619735659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_15 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41774240431259 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098811858057 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨15, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41774240431259 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098811858057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_16 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83513960904519 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197627736937 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨16, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83513960904519 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197627736937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_17 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83479465235083 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197631744687 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨17, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83479465235083 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197631744687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_18 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20861248455177 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098817901071 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨18, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20861248455177 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098817901071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_19 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (83410546628067 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197639797037 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨19, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (83410546628067 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197639797037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13165_0 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (10508650512933 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (439490569823 / 20000000000000 : ℝ))
      (E := (cell13165 ⟨0, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (10508650512933 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (439490569823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_1 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (84034315682171 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197456845337 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨1, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (84034315682171 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197456845337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_2 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (10499931509183 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197460846519 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨2, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (10499931509183 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197460846519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_3 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (10495576655139 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098732430517 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨3, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (10495576655139 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098732430517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_4 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83929799149073 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098734448501 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨4, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83929799149073 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098734448501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_5 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (10486876220187 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (219747290431 / 10000000000000 : ℝ))
      (E := (cell13165 ⟨5, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (10486876220187 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (219747290431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_6 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83860245042717 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197476890497 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨6, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83860245042717 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197476890497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_7 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83825504957257 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098740460433 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨7, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83825504957257 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098740460433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_8 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83790789469827 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (87899397779 / 4000000000000 : ℝ))
      (E := (cell13165 ⟨8, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83790789469827 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (87899397779 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_9 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83756098545317 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098744484053 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨9, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83756098545317 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098744484053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_10 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (16744286429761 / 20000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197492940201 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨10, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (16744286429761 / 20000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197492940201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_11 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83686790245547 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197496983197 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨11, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83686790245547 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197496983197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_12 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83652172800983 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098750493463 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨12, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83652172800983 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098750493463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_13 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (8361757978073 / 10000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098752507633 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨13, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (8361757978073 / 10000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098752507633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_14 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (41791505575293 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197509015577 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨14, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (41791505575293 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197509015577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_15 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83548466876523 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197513051293 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨15, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83548466876523 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197513051293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_16 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (20878486731173 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098758534621 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨16, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (20878486731173 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098758534621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_17 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (41739725630709 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549380268541 / 25000000000000 : ℝ))
      (E := (cell13165 ⟨17, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (41739725630709 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549380268541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_18 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (208612449633 / 250000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549381267641 / 25000000000000 : ℝ))
      (E := (cell13165 ⟨18, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (208612449633 / 250000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549381267641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_19 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (83410532666709 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098764531351 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨19, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (83410532666709 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098764531351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13166_0 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (84069190026441 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098671085479 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨0, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (84069190026441 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098671085479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_1 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (84034301611397 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (109867308179 / 5000000000000 : ℝ))
      (E := (cell13166 ⟨1, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (84034301611397 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (109867308179 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_2 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41999719004467 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197350161209 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨2, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41999719004467 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197350161209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_3 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (4198229959141 / 5000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197354172219 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨3, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (4198229959141 / 5000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197354172219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_4 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41964892548507 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197358204727 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨4, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41964892548507 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197358204727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_5 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (5243437232229 / 6250000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (137335138039 / 6250000000000 : ℝ))
      (E := (cell13166 ⟨5, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (5243437232229 / 6250000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (137335138039 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_6 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (16772046200621 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197366249443 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨6, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (16772046200621 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197366249443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_7 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41912745461931 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098685109249 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨7, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41912745461931 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098685109249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_8 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83790775442641 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197374238837 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨8, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83790775442641 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197374238837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_9 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (5234755282771 / 6250000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (549344564811 / 25000000000000 : ℝ))
      (E := (cell13166 ⟨9, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (5234755282771 / 6250000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (549344564811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_10 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83721418134023 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197382286251 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨10, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83721418134023 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197382286251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_11 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83686776236959 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197386268027 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨11, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83686776236959 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197386268027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_12 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83652158798583 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197390326809 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨12, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83652158798583 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197390326809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_13 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (83617565784513 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197394293977 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨13, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (83617565784513 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197394293977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_14 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41791498580273 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (54934958737 / 2500000000000 : ℝ))
      (E := (cell13166 ⟨14, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41791498580273 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (54934958737 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_15 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (16709690578531 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197402324071 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨15, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (16709690578531 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197402324071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_16 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (8351393294699 / 10000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (549351584781 / 25000000000000 : ℝ))
      (E := (cell13166 ⟨16, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (8351393294699 / 10000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (549351584781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_17 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41739718644939 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197410399449 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨17, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41739718644939 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197410399449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_18 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (16688993177563 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197414393069 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨18, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (16688993177563 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197414393069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_19 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (20852629676869 / 25000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197418382473 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨19, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (20852629676869 / 25000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197418382473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13167_0 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (84069175951559 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197231488591 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨0, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (84069175951559 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197231488591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_1 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (21008571885691 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197235477613 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨1, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (21008571885691 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197235477613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_2 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83999423946543 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197239529593 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨2, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83999423946543 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197239529593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_3 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41982292563333 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098621768561 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨3, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41982292563333 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098621768561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_4 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (20982442761773 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439449513239 / 20000000000000 : ℝ))
      (E := (cell13167 ⟨4, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (20982442761773 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439449513239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_5 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83894981671967 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439450313341 / 20000000000000 : ℝ))
      (E := (cell13167 ⟨5, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83894981671967 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439450313341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_6 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83860216965629 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197255546187 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨6, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83860216965629 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197255546187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_7 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (419127384463 / 500000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439451913989 / 20000000000000 : ℝ))
      (E := (cell13167 ⟨7, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (419127384463 / 500000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439451913989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_8 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83790761417589 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197263587037 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨8, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83790761417589 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197263587037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_9 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (5234754406593 / 6250000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (549316901061 / 25000000000000 : ℝ))
      (E := (cell13167 ⟨9, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (5234754406593 / 6250000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (549316901061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_10 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83721404121373 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098635814049 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨10, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83721404121373 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098635814049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_11 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41843381115251 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197275606769 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨11, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41843381115251 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197275606769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_12 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (83652144798313 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197279662491 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨12, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (83652144798313 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197279662491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_13 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (3344702071617 / 4000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098641842403 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨13, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (3344702071617 / 4000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098641842403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_14 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41791491586317 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439457535837 / 20000000000000 : ℝ))
      (E := (cell13167 ⟨14, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41791491586317 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439457535837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_15 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41774219455457 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (274661463633 / 12500000000000 : ℝ))
      (E := (cell13167 ⟨15, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41774219455457 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (274661463633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_16 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (16702783794283 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197295721267 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨16, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (16702783794283 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197295721267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_17 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41739711660231 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197299720539 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨17, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41739711660231 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197299720539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_18 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (16688990384911 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197303711379 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨18, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (16688990384911 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197303711379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_19 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (16682100950073 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197307756351 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨19, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (16682100950073 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197307756351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13168_0 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (84069161878817 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197120859871 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨0, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (84069161878817 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197120859871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_1 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (84034273476269 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (54928121133 / 2500000000000 : ℝ))
      (E := (cell13168 ⟨1, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (84034273476269 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (54928121133 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_2 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83999409886291 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (219712889377 / 10000000000000 : ℝ))
      (E := (cell13168 ⟨2, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83999409886291 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (219712889377 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_3 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (1679291421453 / 2000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098566448909 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨3, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (1679291421453 / 2000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098566448909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_4 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41964878499653 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197136923459 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨4, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41964878499653 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197136923459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_5 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41947483815203 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197140920583 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨5, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41947483815203 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197140920583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_6 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (5241262683143 / 6250000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (87885795869 / 4000000000000 : ℝ))
      (E := (cell13168 ⟨6, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (5241262683143 / 6250000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (87885795869 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_7 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83825462863473 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197148917189 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨7, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83825462863473 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197148917189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_8 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (8379074739467 / 10000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549288232759 / 25000000000000 : ℝ))
      (E := (cell13168 ⟨8, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (8379074739467 / 10000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549288232759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_9 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83756056488771 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098578472523 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨9, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83756056488771 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098578472523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_10 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41860695055427 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197160965747 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨10, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41860695055427 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197160965747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_11 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41843374113087 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (87886599977 / 4000000000000 : ℝ))
      (E := (cell13168 ⟨11, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41843374113087 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (87886599977 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_12 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20913032700043 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197168993977 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨12, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20913032700043 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197168993977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_13 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (16723507559693 / 20000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (13732331333 / 625000000000 : ℝ))
      (E := (cell13168 ⟨13, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (16723507559693 / 20000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (13732331333 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_14 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83582969186849 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197177062877 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨14, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83582969186849 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197177062877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_15 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83548424931299 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (439436206331 / 20000000000000 : ℝ))
      (E := (cell13168 ⟨15, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83548424931299 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (439436206331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_16 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (16702780999593 / 20000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197185040987 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨16, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (16702780999593 / 20000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197185040987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_17 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83479409353171 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197189095687 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨17, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83479409353171 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197189095687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_18 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41722468981709 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197193083773 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨18, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41722468981709 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197193083773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_19 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (83410490795377 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197197126037 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨19, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (83410490795377 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197197126037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13169_0 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (10508643476027 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (8582071199 / 390625000000 : ℝ))
      (E := (cell13169 ⟨0, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (10508643476027 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (8582071199 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_1 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (42017129705957 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098507133349 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨1, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (42017129705957 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098507133349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_2 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83999395828177 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197018253743 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨2, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83999395828177 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197018253743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_3 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83964557020771 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274627781789 / 12500000000000 : ℝ))
      (E := (cell13169 ⟨3, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83964557020771 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274627781789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_4 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (10491217869207 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (54925656913 / 2500000000000 : ℝ))
      (E := (cell13169 ⟨4, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (10491217869207 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (54925656913 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_5 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83894953590981 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098515135129 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨5, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83894953590981 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098515135129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_6 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83860188897081 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197034301057 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨6, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83860188897081 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197034301057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_7 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83825448836479 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197038318253 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨7, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83825448836479 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197038318253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_8 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83790733373883 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098521164439 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨8, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83790733373883 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098521164439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_9 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (41878021237093 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197046339713 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨9, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (41878021237093 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197046339713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_10 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (16744275220493 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274631294661 / 12500000000000 : ℝ))
      (E := (cell13169 ⟨10, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (16744275220493 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274631294661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_11 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (10460841777997 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439410877577 / 20000000000000 : ℝ))
      (E := (cell13169 ⟨11, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (10460841777997 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439410877577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_12 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83652116804159 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197058379403 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨12, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83652116804159 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197058379403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_13 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (10452190476079 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197062395719 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨13, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (10452190476079 / 12500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197062395719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_14 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83582955203191 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274633305297 / 12500000000000 : ℝ))
      (E := (cell13169 ⟨14, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83582955203191 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274633305297 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_15 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (8354841095381 / 10000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (109853520413 / 5000000000000 : ℝ))
      (E := (cell13169 ⟨15, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (8354841095381 / 10000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (109853520413 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_16 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (83513891026639 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (87882978919 / 4000000000000 : ℝ))
      (E := (cell13169 ⟨16, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (83513891026639 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (87882978919 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_17 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (20869848847001 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439415693329 / 20000000000000 : ℝ))
      (E := (cell13169 ⟨17, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (20869848847001 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439415693329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_18 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (20861231001101 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197082451977 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨18, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (20861231001101 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197082451977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_19 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (8341047684251 / 10000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439417298307 / 20000000000000 : ℝ))
      (E := (cell13169 ⟨19, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (8341047684251 / 10000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439417298307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13170_0 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (42034566869877 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098449823833 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨0, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (42034566869877 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098449823833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_1 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (42017122674849 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (219690362599 / 10000000000000 : ℝ))
      (E := (cell13170 ⟨1, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (42017122674849 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (219690362599 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_2 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (419996908861 / 500000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196907667413 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨2, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (419996908861 / 500000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196907667413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_3 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83964542971029 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (87876466581 / 4000000000000 : ℝ))
      (E := (cell13170 ⟨3, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83964542971029 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (87876466581 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_4 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83929728910143 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (87876627333 / 4000000000000 : ℝ))
      (E := (cell13170 ⟨4, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83929728910143 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (87876627333 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_5 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (8389493955369 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098459836851 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨5, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (8389493955369 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098459836851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_6 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83860174866007 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196923701187 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨6, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83860174866007 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196923701187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_7 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83825434811617 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549231928779 / 25000000000000 : ℝ))
      (E := (cell13170 ⟨7, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83825434811617 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549231928779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_8 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (20947679838807 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (54923293063 / 2500000000000 : ℝ))
      (E := (cell13170 ⟨8, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (20947679838807 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (54923293063 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_9 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (20939007115433 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098467865091 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨9, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (20939007115433 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098467865091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_10 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41860681048103 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196939744629 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨10, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41860681048103 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196939744629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_11 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83686720223907 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196943772147 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨11, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83686720223907 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196943772147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_12 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (3346084112411 / 4000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196947818767 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨12, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (3346084112411 / 4000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196947818767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_13 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41808754910463 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196951832121 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨13, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41808754910463 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196951832121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_14 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83582941221659 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098477908839 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨14, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83582941221659 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098477908839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_15 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41774198489223 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549239959719 / 25000000000000 : ℝ))
      (E := (cell13170 ⟨15, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41774198489223 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549239959719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_16 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41756938528719 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196963842539 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨16, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41756938528719 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2196963842539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_17 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83479381424961 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098483945831 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨17, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83479381424961 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098483945831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_18 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (83444910047513 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439394374853 / 20000000000000 : ℝ))
      (E := (cell13170 ⟨18, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (83444910047513 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439394374853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_19 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (16682092578353 / 20000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (109848795557 / 5000000000000 : ℝ))
      (E := (cell13170 ⟨19, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (16682092578353 / 20000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (109848795557 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13171_0 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (8406911967343 / 10000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274598633023 / 12500000000000 : ℝ))
      (E := (cell13171 ⟨0, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (8406911967343 / 10000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274598633023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_1 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (84034231289619 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196793038959 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨1, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (84034231289619 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196793038959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_2 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (2099984192959 / 2500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (27459963461 / 1250000000000 : ℝ))
      (E := (cell13171 ⟨2, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (2099984192959 / 2500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (27459963461 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_3 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41982264461711 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098400535269 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨3, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41982264461711 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098400535269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_4 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (20982428717191 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196805085931 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨4, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (20982428717191 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196805085931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_5 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41947462759267 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098404565459 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨5, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41947462759267 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098404565459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_6 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83860160837067 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098406577557 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨6, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83860160837067 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098406577557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_7 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (10478177598611 / 12500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196817165799 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨7, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (10478177598611 / 12500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196817165799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_8 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (5236919083669 / 6250000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274602646251 / 12500000000000 : ℝ))
      (E := (cell13171 ⟨8, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (5236919083669 / 6250000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274602646251 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_9 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (5234750903213 / 6250000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (54920629363 / 2500000000000 : ℝ))
      (E := (cell13171 ⟨9, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (5234750903213 / 6250000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (54920629363 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_10 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83721348092077 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439365837173 / 20000000000000 : ℝ))
      (E := (cell13171 ⟨10, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83721348092077 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439365837173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_11 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83686706225967 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098416605163 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨11, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83686706225967 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098416605163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_12 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41826044409259 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098418597901 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨12, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41826044409259 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098418597901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_13 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (20904373958837 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (219684120617 / 10000000000000 : ℝ))
      (E := (cell13171 ⟨13, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (20904373958837 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (219684120617 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_14 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83582927242253 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (549211311743 / 25000000000000 : ℝ))
      (E := (cell13171 ⟨14, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83582927242253 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (549211311743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_15 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83548383005207 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196849265301 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨15, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83548383005207 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196849265301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_16 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83513863090361 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098426633071 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨16, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83513863090361 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098426633071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_17 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (2086984186601 / 2500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (219685731249 / 10000000000000 : ℝ))
      (E := (cell13171 ⟨17, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (2086984186601 / 2500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (219685731249 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_18 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (83444896092743 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439372258473 / 20000000000000 : ℝ))
      (E := (cell13171 ⟨18, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (83444896092743 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439372258473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_19 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41705224471571 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098432663279 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨19, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41705224471571 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098432663279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13172_0 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (42034552804623 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (439335695299 / 20000000000000 : ℝ))
      (E := (cell13172 ⟨0, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (42034552804623 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (439335695299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_1 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (42017108615839 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098341252801 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨1, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (42017108615839 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098341252801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_2 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83999353666657 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098343270023 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨2, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83999353666657 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098343270023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_3 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83964514877951 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098345265137 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨3, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83964514877951 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098345265137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_4 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (1049121260369 / 1250000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098347271141 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨4, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (1049121260369 / 1250000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098347271141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_5 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83894911485511 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098349262981 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨5, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83894911485511 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098349262981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_6 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (4193007340513 / 5000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (549175636711 / 25000000000000 : ℝ))
      (E := (cell13172 ⟨6, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (4193007340513 / 5000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (549175636711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_7 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83825406768291 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274588319283 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨7, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83825406768291 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274588319283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_8 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83790691324311 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196710613297 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨8, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83790691324311 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196710613297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_9 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (16751200088643 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196714614659 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨9, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (16751200088643 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196714614659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_10 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (20930333522519 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274589827863 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨10, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (20930333522519 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274589827863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_11 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (16737338446031 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (219672264431 / 10000000000000 : ℝ))
      (E := (cell13172 ⟨11, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (16737338446031 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (219672264431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_12 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (10456509353611 / 12500000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098363313389 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨12, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (10456509353611 / 12500000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098363313389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_13 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (16723496370379 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274591336543 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨13, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (16723496370379 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274591336543 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_14 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (20895728316243 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274591834009 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨14, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (20895728316243 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274591834009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_15 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83548369034093 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098369343767 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨15, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83548369034093 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098369343767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_16 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (2609807785169 / 3125000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196742685553 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨16, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (2609807785169 / 3125000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196742685553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_17 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41739676752621 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274593341141 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨17, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41739676752621 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274593341141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_18 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (16688976428019 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274593845569 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨18, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (16688976428019 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274593845569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_19 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (83410434996639 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196754737787 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨19, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (83410434996639 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196754737787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13173_0 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (84069091547199 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (109828397123 / 5000000000000 : ℝ))
      (E := (cell13173 ⟨0, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (84069091547199 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (109828397123 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_1 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (42017101587937 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549142992011 / 25000000000000 : ℝ))
      (E := (cell13173 ⟨1, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (42017101587937 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549142992011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_2 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (8399933961709 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196575999011 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨2, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (8399933961709 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196575999011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_3 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (10495562604327 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196579985809 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨3, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (10495562604327 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196579985809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_4 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (8392968679241 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549145998609 / 25000000000000 : ℝ))
      (E := (cell13173 ⟨4, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (8392968679241 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549145998609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_5 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (83894897454621 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196588032753 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨5, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (83894897454621 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196588032753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_6 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (16772026557117 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219659205037 / 10000000000000 : ℝ))
      (E := (cell13173 ⟨6, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (16772026557117 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219659205037 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_7 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (3353015709993 / 4000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549149013643 / 25000000000000 : ℝ))
      (E := (cell13173 ⟨7, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (3353015709993 / 4000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549149013643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_8 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (83790677312049 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196600052391 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨8, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (83790677312049 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196600052391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_9 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (1675119728743 / 2000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098302025303 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨9, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (1675119728743 / 2000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098302025303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_10 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (16744264018041 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196608055749 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨10, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (16744264018041 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196608055749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_11 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (8368667823647 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098306037051 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨11, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (8368667823647 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098306037051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_12 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (16730412168277 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196616111699 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨12, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (16730412168277 / 20000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196616111699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_13 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (10452183483821 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196620116169 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨13, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (10452183483821 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196620116169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_14 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (10447862411227 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098312075583 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨14, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (10447862411227 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098312075583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_15 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (41774177532551 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (274578520473 / 12500000000000 : ℝ))
      (E := (cell13173 ⟨15, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (41774177532551 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (274578520473 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_16 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (83513835162577 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196632159007 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨16, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (83513835162577 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196632159007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_17 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (41739669774283 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196636199831 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨17, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (41739669774283 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196636199831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_18 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (651913032731 / 781250000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (87865606971 / 4000000000000 : ℝ))
      (E := (cell13173 ⟨18, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (651913032731 / 781250000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (87865606971 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_19 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (2606575657883 / 3125000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219664420313 / 10000000000000 : ℝ))
      (E := (cell13173 ⟨19, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (2606575657883 / 3125000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219664420313 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13174_0 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (8406907748729 / 10000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196457404223 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨0, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (8406907748729 / 10000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196457404223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_1 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (42017094561103 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439292285257 / 20000000000000 : ℝ))
      (E := (cell13174 ⟨1, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (42017094561103 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439292285257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_2 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83999325569659 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (87858618151 / 4000000000000 : ℝ))
      (E := (cell13174 ⟨2, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83999325569659 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (87858618151 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_3 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (16792897358683 / 20000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196469495071 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨3, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (16792897358683 / 20000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196469495071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_4 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41964836378717 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (109823675017 / 5000000000000 : ℝ))
      (E := (cell13174 ⟨4, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41964836378717 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (109823675017 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_5 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (10486860428233 / 12500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196477477373 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨5, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (10486860428233 / 12500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196477477373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_6 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41930059381521 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196481491703 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨6, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41930059381521 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196481491703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_7 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (8382537873349 / 10000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (274560686583 / 12500000000000 : ℝ))
      (E := (cell13174 ⟨7, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (8382537873349 / 10000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (274560686583 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_8 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83790663301917 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196489545331 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨8, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83790663301917 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196489545331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_9 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (16751194486643 / 20000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (274561692553 / 12500000000000 : ℝ))
      (E := (cell13174 ⟨9, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (16751194486643 / 20000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (274561692553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_10 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83721306092461 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (219649754249 / 10000000000000 : ℝ))
      (E := (cell13174 ⟨10, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83721306092461 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (219649754249 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_11 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (5230416515307 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098250778907 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨11, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (5230416515307 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098250778907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_12 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (10456505857001 / 12500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (549126398107 / 25000000000000 : ℝ))
      (E := (cell13174 ⟨12, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (10456505857001 / 12500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (549126398107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_13 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41808726945683 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098254796981 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨13, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41808726945683 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098254796981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_14 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (5223930332299 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (219651362607 / 10000000000000 : ℝ))
      (E := (cell13174 ⟨14, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (5223930332299 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (219651362607 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_15 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41774170549117 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098258817923 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨15, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41774170549117 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098258817923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_16 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (20878455300467 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196521628273 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨16, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (20878455300467 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196521628273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_17 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (83479325594011 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196525666347 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨17, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (83479325594011 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196525666347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_18 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (41722427120581 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439305939273 / 20000000000000 : ℝ))
      (E := (cell13174 ⟨18, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (41722427120581 / 50000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439305939273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_19 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (10426300888749 / 12500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196533722589 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨19, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (10426300888749 / 12500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196533722589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

end BstLean.Part268
