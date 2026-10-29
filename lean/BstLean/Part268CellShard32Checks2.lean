import BstLean.Part268CellShard32Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13150_40 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41346443723779 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199276013211 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨40, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41346443723779 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199276013211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_41 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (20664741238227 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099640006281 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨41, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (20664741238227 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099640006281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_42 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (10328133244853 / 12500000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199284040579 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨42, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (10328133244853 / 12500000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199284040579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_43 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41295595217911 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549822024013 / 25000000000000 : ℝ))
      (E := (cell13150 ⟨43, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41295595217911 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549822024013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_44 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (82557338354561 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (87971684747 / 4000000000000 : ℝ))
      (E := (cell13150 ⟨44, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (82557338354561 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (87971684747 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_45 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (20630877421463 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439859221347 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨45, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (20630877421463 / 25000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439859221347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_46 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (82489704400651 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439860023447 / 20000000000000 : ℝ))
      (E := (cell13150 ⟨46, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (82489704400651 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (439860023447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_47 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41227961235029 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099652074053 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨47, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41227961235029 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099652074053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_48 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41211081932661 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549827034521 / 25000000000000 : ℝ))
      (E := (cell13150 ⟨48, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41211081932661 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549827034521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_49 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (82388428557831 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099656101303 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨49, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (82388428557831 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099656101303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_50 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (1029433956489 / 1250000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199316220983 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨50, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (1029433956489 / 1250000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199316220983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_51 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (16464205544173 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (87972807609 / 4000000000000 : ℝ))
      (E := (cell13150 ⟨51, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (16464205544173 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (87972807609 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_52 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41143681067441 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199324225273 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨52, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41143681067441 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199324225273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_53 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (8225371973313 / 10000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549832065941 / 25000000000000 : ℝ))
      (E := (cell13150 ⟨53, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (8225371973313 / 10000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549832065941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_54 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (82220100487707 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549833075537 / 25000000000000 : ℝ))
      (E := (cell13150 ⟨54, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (82220100487707 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549833075537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_55 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (1643730087417 / 2000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549834069381 / 25000000000000 : ℝ))
      (E := (cell13150 ⟨55, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (1643730087417 / 2000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (549834069381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_56 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (16430586270987 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (219934030419 / 10000000000000 : ℝ))
      (E := (cell13150 ⟨56, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (16430586270987 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (219934030419 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_57 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (82119381412473 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (274918039857 / 12500000000000 : ℝ))
      (E := (cell13150 ⟨57, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (82119381412473 / 100000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (274918039857 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_58 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (41042927258057 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099674188179 / 50000000000000 : ℝ))
      (E := (cell13150 ⟨58, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (41042927258057 / 50000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (1099674188179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13150_59 : CellCertificate 13150 (21863299975439 / 250000000000000 : ℝ) (159727698665133 / 100000000000000000 : ℝ) (32238142755831 / 1000000000000000 : ℝ)
    (cell13150 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · norm_num [cell13150]
  · have h := gap_lower (n := 13150) (a := (16410470127729 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199352353709 / 100000000000000 : ℝ))
      (E := (cell13150 ⟨59, by decide⟩).energy) (xi := (32238142755831 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13150 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13150]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13150])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13150) (a := (16410470127729 / 20000000000000 : ℝ)) (b := (7828744777 / 5000000000000 : ℝ)) (q := (2199352353709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13150])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13150]

theorem cert13151_40 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82692873584673 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199165055109 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨40, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82692873584673 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199165055109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_41 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41329475548037 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099584526309 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨41, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41329475548037 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099584526309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_42 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82625052108037 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099586539419 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨42, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82625052108037 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099586539419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_43 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (3303647063643 / 4000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199177073703 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨43, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (3303647063643 / 4000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199177073703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_44 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82557324515851 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099590547299 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨44, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82557324515851 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099590547299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_45 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41261747926587 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199185139883 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨45, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41261747926587 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199185139883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_46 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82489690573999 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549797287193 / 25000000000000 : ℝ))
      (E := (cell13151 ⟨46, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82489690573999 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549797287193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_47 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82455908649429 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549798294519 / 25000000000000 : ℝ))
      (E := (cell13151 ⟨47, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82455908649429 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549798294519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_48 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82422150050709 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (274899645817 / 12500000000000 : ℝ))
      (E := (cell13151 ⟨48, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82422150050709 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (274899645817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_49 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82388414749231 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (137450076849 / 6250000000000 : ℝ))
      (E := (cell13151 ⟨49, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82388414749231 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (137450076849 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_50 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82354702716527 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199205246533 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨50, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82354702716527 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199205246533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_51 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41160506962137 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099604607197 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨51, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41160506962137 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099604607197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_52 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82287348344289 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099606624053 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨52, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82287348344289 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099606624053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_53 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (8225370594853 / 10000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549804321327 / 25000000000000 : ℝ))
      (E := (cell13151 ⟨53, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (8225370594853 / 10000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (549804321327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_54 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (10277510838637 / 12500000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099610661223 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨54, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (10277510838637 / 12500000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099610661223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_55 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41093245299111 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099612648313 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨55, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41093245299111 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099612648313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_56 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (16430583517657 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199229322141 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨56, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (16430583517657 / 20000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199229322141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_57 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (82119367651797 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199233335701 / 100000000000000 : ℝ))
      (E := (cell13151 ⟨57, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (82119367651797 / 100000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (2199233335701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_58 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (1282591261897 / 1562500000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099618696071 / 50000000000000 : ℝ))
      (E := (cell13151 ⟨58, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (1282591261897 / 1562500000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (1099618696071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13151_59 : CellCertificate 13151 (174901173619567 / 2000000000000000 : ℝ) (31943109827847 / 20000000000000000 : ℝ) (20147272132891 / 625000000000000 : ℝ)
    (cell13151 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · norm_num [cell13151]
  · have h := gap_lower (n := 13151) (a := (41026168444951 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (13745258553 / 625000000000 : ℝ))
      (E := (cell13151 ⟨59, by decide⟩).energy) (xi := (20147272132891 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13151 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13151]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13151])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13151) (a := (41026168444951 / 50000000000000 : ℝ)) (b := (39140713429 / 25000000000000 : ℝ)) (q := (13745258553 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13151])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13151]

theorem cert13152_40 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41346429861949 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (109952704641 / 5000000000000 : ℝ))
      (E := (cell13152 ⟨40, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41346429861949 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (109952704641 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_41 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (1653178744827 / 2000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099529044243 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨41, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (1653178744827 / 2000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099529044243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_42 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41312519129679 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199062112911 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨42, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41312519129679 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199062112911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_43 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82591162748437 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099533053013 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨43, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82591162748437 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099533053013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_44 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82557310679249 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099535062609 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨44, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82557310679249 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099535062609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_45 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41261741011301 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099537084423 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨45, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41261741011301 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099537084423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_46 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82489676749453 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (549769544031 / 25000000000000 : ℝ))
      (E := (cell13152 ⟨46, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82489676749453 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (549769544031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_47 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (10306986853863 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (274885275483 / 12500000000000 : ℝ))
      (E := (cell13152 ⟨47, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (10306986853863 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (274885275483 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_48 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (412110681191 / 500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099543124891 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨48, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (412110681191 / 500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099543124891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_49 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82388400942733 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (109954512619 / 5000000000000 : ℝ))
      (E := (cell13152 ⟨49, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82388400942733 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (109954512619 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_50 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (20588672229009 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099547133951 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨50, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (20588672229009 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099547133951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_51 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (10290125016223 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (219909829343 / 10000000000000 : ℝ))
      (E := (cell13152 ⟨51, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (10290125016223 / 12500000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (219909829343 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_52 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (20571833638949 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (274887790729 / 12500000000000 : ℝ))
      (E := (cell13152 ⟨52, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (20571833638949 / 25000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (274887790729 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_53 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82253692166029 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199106302673 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨53, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82253692166029 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199106302673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_54 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (41110036466291 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199110338569 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨54, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (41110036466291 / 50000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199110338569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_55 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (8218647682769 / 10000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099557185347 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨55, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (8218647682769 / 10000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099557185347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_56 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82152903823731 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199118395081 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨56, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82152903823731 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199118395081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_57 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (2566229809163 / 3125000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (54978060189 / 2500000000000 : ℝ))
      (E := (cell13152 ⟨57, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (2566229809163 / 3125000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (54978060189 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_58 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (16417165401759 / 20000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199126403753 / 100000000000000 : ℝ))
      (E := (cell13152 ⟨58, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (16417165401759 / 20000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (2199126403753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13152_59 : CellCertificate 13152 (874479740980419 / 10000000000000000 : ℝ) (159703401461479 / 100000000000000000 : ℝ) (322331284620003 / 10000000000000000 : ℝ)
    (cell13152 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · norm_num [cell13152]
  · have h := gap_lower (n := 13152) (a := (82052323143253 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099565219157 / 50000000000000 : ℝ))
      (E := (cell13152 ⟨59, by decide⟩).energy) (xi := (322331284620003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13152 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13152]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13152])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13152) (a := (82052323143253 / 100000000000000 : ℝ)) (b := (125240651 / 80000000000 : ℝ)) (q := (1099565219157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13152])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13152]

theorem cert13153_40 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41346422932617 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198943126341 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨40, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41346422932617 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198943126341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_41 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16531784677747 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (109947358949 / 5000000000000 : ℝ))
      (E := (cell13153 ⟨41, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16531784677747 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (109947358949 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_42 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (20656256103197 / 25000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099475600817 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨42, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (20656256103197 / 25000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099475600817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_43 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82591148907907 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198955193023 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨43, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82591148907907 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198955193023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_44 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82557296844753 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198959210537 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨44, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82557296844753 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198959210537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_45 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (10315433524267 / 12500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198963252533 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨45, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (10315433524267 / 12500000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198963252533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_46 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (20622415731753 / 25000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (137435453639 / 6250000000000 : ℝ))
      (E := (cell13153 ⟨46, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (20622415731753 / 25000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (137435453639 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_47 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82455881014483 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198971284423 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨47, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82455881014483 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198971284423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_48 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41211061213897 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198975269869 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨48, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41211061213897 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198975269869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_49 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82388387138337 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198979329997 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨49, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82388387138337 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198979329997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_50 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16470935023529 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198983344117 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨50, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16470935023529 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2198983344117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_51 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41160493168697 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (54974682731 / 2500000000000 : ℝ))
      (E := (cell13153 ⟨51, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41160493168697 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (54974682731 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_52 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41143660384701 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549747835077 / 25000000000000 : ℝ))
      (E := (cell13153 ⟨52, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41143660384701 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549747835077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_53 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (41126839192813 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549748843739 / 25000000000000 : ℝ))
      (E := (cell13153 ⟨53, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (41126839192813 / 50000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549748843739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_54 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16444011831633 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099499704817 / 50000000000000 : ℝ))
      (E := (cell13153 ⟨54, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16444011831633 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (1099499704817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_55 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (16437292611851 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2199003440587 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨55, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (16437292611851 / 20000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2199003440587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_56 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82152890061273 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2199007404681 / 100000000000000 : ℝ))
      (E := (cell13153 ⟨56, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82152890061273 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (2199007404681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_57 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (8211934013673 / 10000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (439802295049 / 20000000000000 : ℝ))
      (E := (cell13153 ⟨57, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (8211934013673 / 10000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (439802295049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_58 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (20521453314569 / 25000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549753867601 / 25000000000000 : ℝ))
      (E := (cell13153 ⟨58, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (20521453314569 / 25000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (549753867601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13153_59 : CellCertificate 13153 (874453617664441 / 10000000000000000 : ℝ) (798456278157217 / 500000000000000000 : ℝ) (322306219038579 / 10000000000000000 : ℝ)
    (cell13153 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · norm_num [cell13153]
  · have h := gap_lower (n := 13153) (a := (82052309398697 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274877437997 / 12500000000000 : ℝ))
      (E := (cell13153 ⟨59, by decide⟩).energy) (xi := (322306219038579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13153 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13153]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13153])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13153) (a := (82052309398697 / 100000000000000 : ℝ)) (b := (78269387821 / 50000000000000 : ℝ)) (q := (274877437997 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13153])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13153]

theorem cert13154_40 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82692832008679 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439766442893 / 20000000000000 : ℝ))
      (E := (cell13154 ⟨40, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82692832008679 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (439766442893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_41 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82658909538229 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198836265287 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨41, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82658909538229 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198836265287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_42 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (41312505284163 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099420113667 / 50000000000000 : ℝ))
      (E := (cell13154 ⟨42, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (41312505284163 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099420113667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_43 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82591135069483 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549711068959 / 25000000000000 : ℝ))
      (E := (cell13154 ⟨43, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82591135069483 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549711068959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_44 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82557283012363 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274856036459 / 12500000000000 : ℝ))
      (E := (cell13154 ⟨44, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82557283012363 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274856036459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_45 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (3300938174711 / 4000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549713083009 / 25000000000000 : ℝ))
      (E := (cell13154 ⟨45, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (3300938174711 / 4000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (549713083009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_46 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (3299585964267 / 4000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198856336141 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨46, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (3299585964267 / 4000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198856336141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_47 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (16491173440033 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198860360801 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨47, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (16491173440033 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198860360801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_48 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (8242210861949 / 10000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198864344753 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨48, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (8242210861949 / 10000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198864344753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_49 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82388373336043 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198868403433 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨49, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82388373336043 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198868403433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_50 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (20588665330339 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198872416151 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨50, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (20588665330339 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198872416151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_51 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (2572530392097 / 3125000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274859554871 / 12500000000000 : ℝ))
      (E := (cell13154 ⟨51, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (2572530392097 / 3125000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (274859554871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_52 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82287306985107 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198880409677 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨52, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82287306985107 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198880409677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_53 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82253664607321 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099442221531 / 50000000000000 : ℝ))
      (E := (cell13154 ⟨53, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82253664607321 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099442221531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_54 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (16444009077169 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198888476523 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨54, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (16444009077169 / 20000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198888476523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_55 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (20546612323229 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (34357695411 / 1562500000000 : ℝ))
      (E := (cell13154 ⟨55, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (20546612323229 / 25000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (34357695411 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_56 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82152876300909 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198896528439 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨56, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82152876300909 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198896528439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_57 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (41059663191169 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198900538757 / 100000000000000 : ℝ))
      (E := (cell13154 ⟨57, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (41059663191169 / 50000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (2198900538757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_58 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (1641715990197 / 2000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099452266441 / 50000000000000 : ℝ))
      (E := (cell13154 ⟨58, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (1641715990197 / 2000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099452266441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13154_59 : CellCertificate 13154 (87442749814903 / 1000000000000000 : ℝ) (798395558243533 / 500000000000000000 : ℝ) (161140578690507 / 5000000000000000 : ℝ)
    (cell13154 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · norm_num [cell13154]
  · have h := gap_lower (n := 13154) (a := (82052295656233 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099454282733 / 50000000000000 : ℝ))
      (E := (cell13154 ⟨59, by decide⟩).energy) (xi := (161140578690507 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13154 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13154]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13154])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13154) (a := (82052295656233 / 100000000000000 : ℝ)) (b := (2445730303 / 1562500000000 : ℝ)) (q := (1099454282733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13154])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13154]

theorem cert13155_40 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41346409077117 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198721298401 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨40, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41346409077117 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198721298401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_41 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (10332361961229 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (137420334213 / 6250000000000 : ℝ))
      (E := (cell13155 ⟨41, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (10332361961229 / 12500000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (137420334213 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_42 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82624996725971 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198729366523 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨42, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82624996725971 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198729366523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_43 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41295560616583 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439746670893 / 20000000000000 : ℝ))
      (E := (cell13155 ⟨43, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41295560616583 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439746670893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_44 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82557269182079 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198737368623 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨44, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82557269182079 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198737368623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_45 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82523440543519 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549685351839 / 25000000000000 : ℝ))
      (E := (cell13155 ⟨45, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82523440543519 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549685351839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_46 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41244817644221 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198745409877 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨46, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41244817644221 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198745409877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_47 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (1649117067759 / 2000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099374716499 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨47, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (1649117067759 / 2000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099374716499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_48 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82422094813289 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439750694887 / 20000000000000 : ℝ))
      (E := (cell13155 ⟨48, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82422094813289 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (439750694887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_49 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (1647767190717 / 2000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (219875747269 / 10000000000000 : ℝ))
      (E := (cell13155 ⟨49, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (1647767190717 / 2000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (219875747269 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_50 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41177323763583 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (274845185501 / 12500000000000 : ℝ))
      (E := (cell13155 ⟨50, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41177323763583 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (274845185501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_51 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41160479379457 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198765505469 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨51, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41160479379457 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198765505469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_52 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (8228729320291 / 10000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198769533943 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨52, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (8228729320291 / 10000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198769533943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_53 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41126825415557 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (274846695761 / 12500000000000 : ℝ))
      (E := (cell13155 ⟨53, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41126825415557 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (274846695761 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_54 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41110015807811 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549694399589 / 25000000000000 : ℝ))
      (E := (cell13155 ⟨54, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41110015807811 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (549694399589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_55 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82186435528673 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198781567847 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨55, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82186435528673 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198781567847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_56 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82152862542641 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198785588857 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨56, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82152862542641 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198785588857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_57 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (82119312630039 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099394828643 / 50000000000000 : ℝ))
      (E := (cell13155 ⟨57, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (82119312630039 / 100000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (1099394828643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_58 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41042892881759 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198793650401 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨58, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41042892881759 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198793650401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13155_59 : CellCertificate 13155 (437200691216659 / 5000000000000000 : ℝ) (1596669695128473 / 1000000000000000000 : ℝ) (2517625778487 / 78125000000000 : ℝ)
    (cell13155 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · norm_num [cell13155]
  · have h := gap_lower (n := 13155) (a := (41026140957931 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198797682021 / 100000000000000 : ℝ))
      (E := (cell13155 ⟨59, by decide⟩).energy) (xi := (2517625778487 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13155 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13155]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13155])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13155) (a := (41026140957931 / 50000000000000 : ℝ)) (b := (156514704999 / 100000000000000 : ℝ)) (q := (2198797682021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13155])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13155]

theorem cert13156_40 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41346402150949 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198610436943 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨40, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41346402150949 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198610436943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_41 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41329440921771 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198614484159 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨41, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41329440921771 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198614484159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_42 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82624982885723 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198618501529 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨42, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82624982885723 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198618501529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_43 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (16518221479791 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549655621943 / 25000000000000 : ℝ))
      (E := (cell13156 ⟨43, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (16518221479791 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549655621943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_44 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (825572553539 / 1000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198626500277 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨44, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (825572553539 / 1000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198626500277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_45 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82523426721367 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198630537403 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨45, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82523426721367 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198630537403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_46 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (10311202684039 / 12500000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198634538363 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨46, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (10311202684039 / 12500000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198634538363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_47 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82455839577837 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219863855997 / 10000000000000 : ℝ))
      (E := (cell13156 ⟨47, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82455839577837 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (219863855997 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_48 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (20605520252297 / 25000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198642599939 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨48, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (20605520252297 / 25000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198642599939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_49 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82388345737757 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198646596771 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨49, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82388345737757 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198646596771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_50 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (20588658433769 / 25000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198650606713 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨50, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (20588658433769 / 25000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198650606713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_51 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82320944972821 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549663656711 / 25000000000000 : ℝ))
      (E := (cell13156 ⟨51, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82320944972821 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549663656711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_52 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82287279422811 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198658654033 / 100000000000000 : ℝ))
      (E := (cell13156 ⟨52, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82287279422811 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (2198658654033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_53 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82253637057003 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (109933134247 / 5000000000000 : ℝ))
      (E := (cell13156 ⟨53, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82253637057003 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (109933134247 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_54 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (16444003569499 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439733343203 / 20000000000000 : ℝ))
      (E := (cell13156 ⟨54, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (16444003569499 / 20000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439733343203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_55 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (20546605441631 / 25000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099335371751 / 50000000000000 : ℝ))
      (E := (cell13156 ⟨55, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (20546605441631 / 25000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1099335371751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_56 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82152848786467 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439734952687 / 20000000000000 : ℝ))
      (E := (cell13156 ⟨56, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82152848786467 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (439734952687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_57 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (41059649439917 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549669692911 / 25000000000000 : ℝ))
      (E := (cell13156 ⟨57, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (41059649439917 / 50000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (549669692911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_58 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82085772019277 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1758946211 / 80000000000 : ℝ))
      (E := (cell13156 ⟨58, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82085772019277 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (1758946211 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13156_59 : CellCertificate 13156 (874375270516433 / 10000000000000000 : ℝ) (798274146117221 / 500000000000000000 : ℝ) (12889241833343 / 400000000000000 : ℝ)
    (cell13156 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · norm_num [cell13156]
  · have h := gap_lower (n := 13156) (a := (82052268177581 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (274835849301 / 12500000000000 : ℝ))
      (E := (cell13156 ⟨59, by decide⟩).energy) (xi := (12889241833343 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13156 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13156]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13156])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13156) (a := (82052268177581 / 100000000000000 : ℝ)) (b := (156502672463 / 100000000000000 : ℝ)) (q := (274835849301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13156])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13156]

theorem cert13157_40 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (8269279045167 / 10000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (21984995713 / 1000000000000 : ℝ))
      (E := (cell13157 ⟨40, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (8269279045167 / 10000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (21984995713 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_41 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (129154481249 / 156250000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099251808363 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨41, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (129154481249 / 156250000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099251808363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_42 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41312484523791 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198507632351 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨42, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41312484523791 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198507632351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_43 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (1651821871337 / 2000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (17175872007 / 781250000000 : ℝ))
      (E := (cell13157 ⟨43, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (1651821871337 / 2000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (17175872007 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_44 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (3302289661113 / 4000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (8794062511 / 400000000000 : ℝ))
      (E := (cell13157 ⟨44, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (3302289661113 / 4000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (8794062511 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_45 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41261706450659 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198519663271 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨45, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41261706450659 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198519663271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_46 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (16497921531657 / 20000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (219852366267 / 10000000000000 : ℝ))
      (E := (cell13157 ⟨46, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (16497921531657 / 20000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (219852366267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_47 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41227912884913 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198527682763 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨47, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41227912884913 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198527682763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_48 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82422067207189 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (439706344253 / 20000000000000 : ℝ))
      (E := (cell13157 ⟨48, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82422067207189 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (439706344253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_49 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (20597082985441 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (549633929169 / 25000000000000 : ℝ))
      (E := (cell13157 ⟨49, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (20597082985441 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (549633929169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_50 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (16470923989017 / 20000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198539784267 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨50, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (16470923989017 / 20000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198539784267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_51 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (20580232797207 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198543803091 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨51, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (20580232797207 / 25000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198543803091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_52 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82287265644809 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198547829021 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨52, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82287265644809 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198547829021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_53 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82253623284989 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198551799617 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨53, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82253623284989 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198551799617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_54 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82220004081463 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099277914751 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨54, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82220004081463 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099277914751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_55 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82186408006471 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198559855843 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨55, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82186408006471 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198559855843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_56 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41076417516193 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198563874677 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨56, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41076417516193 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198563874677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_57 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (41059642565861 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274820985229 / 12500000000000 : ℝ))
      (E := (cell13157 ⟨57, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (41059642565861 / 50000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (274820985229 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_58 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (82085758277129 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198571932143 / 100000000000000 : ℝ))
      (E := (cell13157 ⟨58, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (82085758277129 / 100000000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (2198571932143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13157_59 : CellCertificate 13157 (874349162397507 / 10000000000000000 : ℝ) (1596426907800761 / 1000000000000000000 : ℝ) (322205995941761 / 10000000000000000 : ℝ)
    (cell13157 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · norm_num [cell13157]
  · have h := gap_lower (n := 13157) (a := (5128265902587 / 6250000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099287980931 / 50000000000000 : ℝ))
      (E := (cell13157 ⟨59, by decide⟩).energy) (xi := (322205995941761 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13157 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13157]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13157])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13157) (a := (5128265902587 / 6250000000000 : ℝ)) (b := (156490641783 / 100000000000000 : ℝ)) (q := (1099287980931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13157])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13157]

theorem cert13158_40 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (1653855532071 / 2000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (274798595033 / 12500000000000 : ℝ))
      (E := (cell13158 ⟨40, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (1653855532071 / 2000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (274798595033 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_41 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (16531770831457 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (219839274511 / 10000000000000 : ℝ))
      (E := (cell13158 ⟨41, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (16531770831457 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (219839274511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_42 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82624955211547 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198396758991 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨42, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82624955211547 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198396758991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_43 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82591079736849 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198400800701 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨43, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82591079736849 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198400800701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_44 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (16511445540771 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099202404963 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨44, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (16511445540771 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099202404963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_45 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82523399083373 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099204421933 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨45, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82523399083373 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099204421933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_46 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (2062239846159 / 2500000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (219841284173 / 10000000000000 : ℝ))
      (E := (cell13158 ⟨46, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (2062239846159 / 2500000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (219841284173 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_47 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82455811963917 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198416860333 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨47, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82455811963917 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198416860333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_48 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (8242205340729 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (137401306087 / 6250000000000 : ℝ))
      (E := (cell13158 ⟨48, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (8242205340729 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (137401306087 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_49 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82388318147871 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439684978281 / 20000000000000 : ℝ))
      (E := (cell13158 ⟨49, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82388318147871 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (439684978281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_50 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82354606157193 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (109921444931 / 5000000000000 : ℝ))
      (E := (cell13158 ⟨50, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82354606157193 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (109921444931 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_51 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82320917406931 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198432916117 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨51, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82320917406931 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198432916117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_52 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (16457450373781 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099218470381 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨52, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (16457450373781 / 20000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099218470381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_53 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (8225360951507 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198440969219 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨53, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (8225360951507 / 10000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198440969219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_54 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82219990317527 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (137402812371 / 6250000000000 : ℝ))
      (E := (cell13158 ⟨54, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82219990317527 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (137402812371 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_55 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82186394248511 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (549612255789 / 25000000000000 : ℝ))
      (E := (cell13158 ⟨55, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82186394248511 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (549612255789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_56 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82152821280399 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099226520457 / 50000000000000 : ℝ))
      (E := (cell13158 ⟨56, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82152821280399 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (1099226520457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_57 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (41059635692851 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (214693071 / 9765625000 : ℝ))
      (E := (cell13158 ⟨57, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (41059635692851 / 50000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (214693071 / 9765625000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_58 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (5130359033567 / 6250000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198461096367 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨58, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (5130359033567 / 6250000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198461096367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13158_59 : CellCertificate 13158 (874323058075671 / 10000000000000000 : ℝ) (79815277091161 / 50000000000000000 : ℝ) (12887237998797 / 400000000000000 : ℝ)
    (cell13158 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · norm_num [cell13158]
  · have h := gap_lower (n := 13158) (a := (82052240707293 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198465125149 / 100000000000000 : ℝ))
      (E := (cell13158 ⟨59, by decide⟩).energy) (xi := (12887237998797 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13158 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13158]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13158])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13158) (a := (82052240707293 / 100000000000000 : ℝ)) (b := (156478612959 / 100000000000000 : ℝ)) (q := (2198465125149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13158])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13158]

theorem cert13159_40 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82692762757537 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099138972523 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨40, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82692762757537 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099138972523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_41 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (20664710079329 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198281928127 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨41, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (20664710079329 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198281928127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_42 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82624941377617 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198285940289 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨42, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82624941377617 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198285940289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_43 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41295532954477 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (87931599213 / 4000000000000 : ℝ))
      (E := (cell13159 ⟨43, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41295532954477 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (87931599213 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_44 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82557213881989 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549573496981 / 25000000000000 : ℝ))
      (E := (cell13159 ⟨44, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82557213881989 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (549573496981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_45 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82523385267531 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198298020283 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨45, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82523385267531 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198298020283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_46 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82489580036537 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198302016613 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨46, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82489580036537 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198302016613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_47 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (20613949540027 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (34348531777 / 1562500000000 : ℝ))
      (E := (cell13159 ⟨47, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (20613949540027 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (34348531777 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_48 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82422039609491 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (68697189667 / 3125000000000 : ℝ))
      (E := (cell13159 ⟨48, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82422039609491 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (68697189667 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_49 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82388304356077 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198314061961 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨49, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82388304356077 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198314061961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_50 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82354592371399 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198318126851 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨50, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82354592371399 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198318126851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_51 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82320903627133 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099161071533 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨51, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82320903627133 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099161071533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_52 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (10285904761887 / 12500000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099163083239 / 50000000000000 : ℝ))
      (E := (cell13159 ⟨52, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (10285904761887 / 12500000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (1099163083239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_53 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (82253595747247 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (43966602693 / 2000000000000 : ℝ))
      (E := (cell13159 ⟨53, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (82253595747247 / 100000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (43966602693 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_54 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (16443995311137 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198334162199 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨54, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (16443995311137 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198334162199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_55 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (16437276098529 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198338186299 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨55, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (16437276098529 / 20000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198338186299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_56 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (10269100941313 / 12500000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198342202983 / 100000000000000 : ℝ))
      (E := (cell13159 ⟨56, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (10269100941313 / 12500000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (2198342202983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_57 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41059628820887 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (219834626727 / 10000000000000 : ℝ))
      (E := (cell13159 ⟨57, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41059628820887 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (219834626727 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_58 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (41042865399553 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (87934010257 / 4000000000000 : ℝ))
      (E := (cell13159 ⟨58, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (41042865399553 / 50000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (87934010257 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13159_59 : CellCertificate 13159 (174859391510011 / 2000000000000000 : ℝ) (159618419429761 / 100000000000000000 : ℝ) (322155907917097 / 10000000000000000 : ℝ)
    (cell13159 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · norm_num [cell13159]
  · have h := gap_lower (n := 13159) (a := (20513056743821 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (219835428427 / 10000000000000 : ℝ))
      (E := (cell13159 ⟨59, by decide⟩).energy) (xi := (322155907917097 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13159 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13159]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13159])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13159) (a := (20513056743821 / 25000000000000 : ℝ)) (b := (15646658599 / 10000000000000 : ℝ)) (q := (219835428427 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13159])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13159]

theorem cert13160_40 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82692748913631 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198167125647 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨40, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82692748913631 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198167125647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_41 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82658826479453 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198171165777 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨41, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82658826479453 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198171165777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_42 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (1291014492903 / 1562500000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (439635035249 / 20000000000000 : ℝ))
      (E := (cell13160 ⟨42, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (1291014492903 / 1562500000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (439635035249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_43 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41295526041581 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198179155771 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨43, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41295526041581 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198179155771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_44 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (3302288002489 / 4000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198183220629 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨44, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (3302288002489 / 4000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198183220629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_45 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82523371453791 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198187192523 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨45, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82523371453791 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198187192523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_46 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (16497913245763 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198191246251 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨46, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (16497913245763 / 20000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198191246251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_47 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (6441858153 / 7812500000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099097630951 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨47, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (6441858153 / 7812500000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099097630951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_48 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (2575688306681 / 3125000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198199296099 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨48, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (2575688306681 / 3125000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198199296099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_49 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41194145283191 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (137387705459 / 6250000000000 : ℝ))
      (E := (cell13160 ⟨49, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41194145283191 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (137387705459 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_50 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82354578587703 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099103645941 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨50, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82354578587703 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099103645941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_51 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82320889849431 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099105653397 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨51, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82320889849431 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099105653397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_52 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (10285903040423 / 12500000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549553832237 / 25000000000000 : ℝ))
      (E := (cell13160 ⟨52, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (10285903040423 / 12500000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549553832237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_53 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (1028169774769 / 1250000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549554838751 / 25000000000000 : ℝ))
      (E := (cell13160 ⟨53, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (1028169774769 / 1250000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (549554838751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_54 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (82219962795937 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198223381413 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨54, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (82219962795937 / 100000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198223381413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_55 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (10273295842359 / 12500000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198227404417 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨55, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (10273295842359 / 12500000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198227404417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_56 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41076396891351 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (43964628401 / 2000000000000 : ℝ))
      (E := (cell13160 ⟨56, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41076396891351 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (43964628401 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_57 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (41059621949969 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099117712071 / 50000000000000 : ℝ))
      (E := (cell13160 ⟨57, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (41059621949969 / 50000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (1099117712071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_58 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (8208571706323 / 10000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198239471529 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨58, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (8208571706323 / 10000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198239471529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13160_59 : CellCertificate 13160 (87427086081979 / 1000000000000000 : ℝ) (1596062865219723 / 1000000000000000000 : ℝ) (322130869782307 / 10000000000000000 : ℝ)
    (cell13160 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · norm_num [cell13160]
  · have h := gap_lower (n := 13160) (a := (20513053311341 / 25000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198243498463 / 100000000000000 : ℝ))
      (E := (cell13160 ⟨59, by decide⟩).energy) (xi := (322130869782307 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13160 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13160]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13160])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13160) (a := (20513053311341 / 25000000000000 : ℝ)) (b := (39113640219 / 25000000000000 : ℝ)) (q := (2198243498463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13160])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13160]

theorem cert13161_40 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (10336591883979 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198056360857 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨40, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (10336591883979 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198056360857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_41 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (5166175790231 / 6250000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198060340433 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨41, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (5166175790231 / 6250000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198060340433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_42 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (10328114214509 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198064408021 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨42, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (10328114214509 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198064408021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_43 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41295519129737 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (21980683859 / 1000000000000 : ℝ))
      (E := (cell13161 ⟨43, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41295519129737 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (21980683859 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_44 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (16511437248913 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198072390271 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨44, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (16511437248913 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198072390271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_45 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (82523357642153 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099038209747 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨45, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (82523357642153 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099038209747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_46 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (16497910484639 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198080471713 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨46, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (16497910484639 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198080471713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_47 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (10306971319849 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198084485901 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨47, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (10306971319849 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198084485901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_48 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (2575687875631 / 3125000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198088518681 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨48, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (2575687875631 / 3125000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198088518681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_49 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (16477655355757 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099046254277 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨49, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (16477655355757 / 20000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099046254277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_50 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (10294320600763 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198096511767 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨50, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (10294320600763 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198096511767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_51 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (3292835042953 / 4000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (10990502627 / 500000000000 : ℝ))
      (E := (cell13161 ⟨51, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (3292835042953 / 4000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (10990502627 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_52 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41143605276883 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099052273161 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨52, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41143605276883 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099052273161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_53 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41126784108943 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (219810857119 / 10000000000000 : ℝ))
      (E := (cell13161 ⟨53, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41126784108943 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (219810857119 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_54 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41109974519141 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198112596457 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨54, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41109974519141 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198112596457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_55 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (10273294123399 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439623323673 / 20000000000000 : ℝ))
      (E := (cell13161 ⟨55, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (10273294123399 / 12500000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (439623323673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_56 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (82152780036991 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (43962412659 / 2000000000000 : ℝ))
      (E := (cell13161 ⟨56, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (82152780036991 / 100000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (43962412659 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_57 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (1283112971253 / 1562500000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099062318019 / 50000000000000 : ℝ))
      (E := (cell13161 ⟨57, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (1283112971253 / 1562500000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (1099062318019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_58 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (20521425832361 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (549532170617 / 25000000000000 : ℝ))
      (E := (cell13161 ⟨58, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (20521425832361 / 25000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (549532170617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13161_59 : CellCertificate 13161 (874244767884009 / 10000000000000000 : ℝ) (1595941554585353 / 1000000000000000000 : ℝ) (322105835564589 / 10000000000000000 : ℝ)
    (cell13161 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · norm_num [cell13161]
  · have h := gap_lower (n := 13161) (a := (41026099758767 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198132708489 / 100000000000000 : ℝ))
      (E := (cell13161 ⟨59, by decide⟩).energy) (xi := (322105835564589 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13161 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13161]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13161])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13161) (a := (41026099758767 / 50000000000000 : ℝ)) (b := (156442537617 / 100000000000000 : ℝ)) (q := (2198132708489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13161])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13161]

theorem cert13162_40 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (41346360616069 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197945591889 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨40, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (41346360616069 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197945591889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_41 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82658798810043 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197949628541 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨41, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82658798810043 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197949628541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_42 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (10328112486057 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197953635621 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨42, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (10328112486057 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197953635621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_43 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82591024437889 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197957611853 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨43, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82591024437889 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197957611853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_44 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (41278586214503 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (549490418377 / 25000000000000 : ℝ))
      (E := (cell13162 ⟨44, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (41278586214503 / 50000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (549490418377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_45 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (10315417979077 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (5494914253 / 250000000000 : ℝ))
      (E := (cell13162 ⟨45, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (10315417979077 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (5494914253 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_46 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (3299581544787 / 4000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197969693001 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨46, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (3299581544787 / 4000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197969693001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_47 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20613939190321 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098986852863 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨47, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20613939190321 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098986852863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_48 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82421998228691 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (219797773709 / 10000000000000 : ℝ))
      (E := (cell13162 ⟨48, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82421998228691 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (219797773709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_49 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (16477652598657 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098990862797 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨49, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (16477652598657 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098990862797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_50 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82354551026601 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197985786509 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨50, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82354551026601 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2197985786509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_51 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (16464172460063 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098994899443 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨51, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (16464172460063 / 20000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098994899443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_52 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20571799196561 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098996909299 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨52, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20571799196561 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1098996909299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_53 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82253554456347 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (17171858143 / 781250000000 : ℝ))
      (E := (cell13162 ⟨53, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82253554456347 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (17171858143 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_54 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (82219935282721 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1099000933227 / 50000000000000 : ℝ))
      (E := (cell13162 ⟨54, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (82219935282721 / 100000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (1099000933227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_55 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20546584809401 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (549501471823 / 25000000000000 : ℝ))
      (E := (cell13162 ⟨55, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20546584809401 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (549501471823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_56 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20538191573343 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (43960198017 / 2000000000000 : ℝ))
      (E := (cell13162 ⟨56, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20538191573343 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (43960198017 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_57 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (10264902052817 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2198013902961 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨57, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (10264902052817 / 12500000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2198013902961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_58 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (20521422399437 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2198017948457 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨58, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (20521422399437 / 25000000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2198017948457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13162_59 : CellCertificate 13162 (874218678741843 / 10000000000000000 : ℝ) (797910131195147 / 500000000000000000 : ℝ) (322080805262973 / 10000000000000000 : ℝ)
    (cell13162 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · norm_num [cell13162]
  · have h := gap_lower (n := 13162) (a := (5128261611987 / 6250000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2198021973591 / 100000000000000 : ℝ))
      (E := (cell13162 ⟨59, by decide⟩).energy) (xi := (322080805262973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13162 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13162]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13162])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13162) (a := (5128261611987 / 6250000000000 : ℝ)) (b := (156430516211 / 100000000000000 : ℝ)) (q := (2198021973591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13162])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13162]

theorem cert13163_40 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (1653854147891 / 2000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (549458719383 / 25000000000000 : ℝ))
      (E := (cell13163 ⟨40, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (1653854147891 / 2000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (549458719383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_41 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (1291543515289 / 1562500000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197838853653 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨41, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (1291543515289 / 1562500000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197838853653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_42 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82624886062943 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197842859043 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨42, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82624886062943 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197842859043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_43 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82591010618407 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197846892489 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨43, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82591010618407 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197846892489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_44 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (1651143172311 / 2000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197850893683 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨44, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (1651143172311 / 2000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197850893683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_45 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (4126166501259 / 5000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197854919821 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨45, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (4126166501259 / 5000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197854919821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_46 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (41244762409127 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197858969047 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨46, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (41244762409127 / 50000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197858969047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_47 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (659645943727 / 800000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197862980333 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨47, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (659645943727 / 800000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197862980333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_48 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82421984439287 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098933505153 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨48, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82421984439287 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098933505153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_49 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82388249209883 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197870997463 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨49, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82388249209883 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197870997463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_50 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (16470907449839 / 20000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098937528539 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨50, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (16470907449839 / 20000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098937528539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_51 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82320848528901 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197879068201 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨51, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82320848528901 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197879068201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_52 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82287183020817 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (439576617341 / 20000000000000 : ℝ))
      (E := (cell13163 ⟨52, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82287183020817 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (439576617341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_53 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82253540696901 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197887109249 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨53, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82253540696901 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197887109249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_54 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82219921529253 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197891132283 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨54, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82219921529253 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197891132283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_55 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (20546581372527 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (43957903041 / 2000000000000 : ℝ))
      (E := (cell13163 ⟨55, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (20546581372527 / 25000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (43957903041 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_56 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82152752551843 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098949582293 / 50000000000000 : ℝ))
      (E := (cell13163 ⟨56, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82152752551843 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (1098949582293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_57 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82119202686971 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197903165717 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨57, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82119202686971 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197903165717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_58 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82085675868141 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197907210281 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨58, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82085675868141 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197907210281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13163_59 : CellCertificate 13163 (109274074174053 / 1250000000000000 : ℝ) (1595698988630343 / 1000000000000000000 : ℝ) (80513944719123 / 2500000000000000 : ℝ)
    (cell13163 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · norm_num [cell13163]
  · have h := gap_lower (n := 13163) (a := (82052172068139 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197911234529 / 100000000000000 : ℝ))
      (E := (cell13163 ⟨59, by decide⟩).energy) (xi := (80513944719123 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13163 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13163]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13163])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13163) (a := (82052172068139 / 100000000000000 : ℝ)) (b := (7820924833 / 5000000000000 : ℝ)) (q := (2197911234529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13163])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13163]

theorem cert13164_40 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82692693559067 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098862079499 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨40, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82692693559067 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098862079499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_41 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20664692787263 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098864066703 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨41, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20664692787263 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098864066703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_42 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41312436119767 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197732137127 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨42, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41312436119767 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197732137127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_43 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20647749200257 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197736168951 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨43, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20647749200257 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197736168951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_44 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41278572402097 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (17169845527 / 781250000000 : ℝ))
      (E := (cell13164 ⟨44, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41278572402097 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (17169845527 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_45 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20630829054961 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197744193179 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨45, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20630829054961 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197744193179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_46 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41244755509467 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197748240921 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨46, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41244755509467 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197748240921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_47 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20613932293141 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (219775225077 / 10000000000000 : ℝ))
      (E := (cell13164 ⟨47, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20613932293141 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (219775225077 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_48 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82421970651981 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (274719534919 / 12500000000000 : ℝ))
      (E := (cell13164 ⟨48, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82421970651981 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (274719534919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_49 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82388235428577 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098880162083 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨49, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82388235428577 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098880162083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_50 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (16470904694777 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197764323479 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨50, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (16470904694777 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197764323479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_51 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82320834759581 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197768333349 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨51, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82320834759581 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197768333349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_52 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82287169257483 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098886175323 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨52, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82287169257483 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098886175323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_53 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20563381734887 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197776372029 / 100000000000000 : ℝ))
      (E := (cell13164 ⟨53, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20563381734887 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (2197776372029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_54 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (20554976944469 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (549445098487 / 25000000000000 : ℝ))
      (E := (cell13164 ⟨54, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (20554976944469 / 25000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (549445098487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_55 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82186311744703 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098892206323 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨55, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82186311744703 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098892206323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_56 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (16430547762481 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098894212079 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨56, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (16430547762481 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098894212079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_57 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (16423837790699 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (274724053039 / 12500000000000 : ℝ))
      (E := (cell13164 ⟨57, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (16423837790699 / 20000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (274724053039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_58 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (41042831070311 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (439559293589 / 20000000000000 : ℝ))
      (E := (cell13164 ⟨58, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (41042831070311 / 50000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (439559293589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13164_59 : CellCertificate 13164 (174833302366977 / 2000000000000000 : ℝ) (797788866650649 / 500000000000000000 : ℝ) (322030756404179 / 10000000000000000 : ℝ)
    (cell13164 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · norm_num [cell13164]
  · have h := gap_lower (n := 13164) (a := (82052158346573 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098900245653 / 50000000000000 : ℝ))
      (E := (cell13164 ⟨59, by decide⟩).energy) (xi := (322030756404179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13164 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13164]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13164])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13164) (a := (82052158346573 / 100000000000000 : ℝ)) (b := (156406478961 / 100000000000000 : ℝ)) (q := (1098900245653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13164])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13164]

theorem cert13165_40 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (10336584965711 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (17168854971 / 781250000000 : ℝ))
      (E := (cell13165 ⟨40, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (10336584965711 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (17168854971 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_41 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (5166172332607 / 6250000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549404366949 / 25000000000000 : ℝ))
      (E := (cell13165 ⟨41, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (5166172332607 / 6250000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549404366949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_42 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82624858418227 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098810734937 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨42, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82624858418227 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098810734937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_43 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82590982985749 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197625500101 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨43, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82590982985749 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197625500101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_44 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (4127856549747 / 5000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (274703687271 / 12500000000000 : ℝ))
      (E := (cell13165 ⟨44, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (4127856549747 / 5000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (274703687271 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_45 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82523302416609 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197633521271 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨45, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82523302416609 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197633521271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_46 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (5155593576357 / 6250000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (439527513511 / 20000000000000 : ℝ))
      (E := (cell13165 ⟨46, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (5155593576357 / 6250000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (439527513511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_47 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82455715381351 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197641575991 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨47, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82455715381351 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197641575991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_48 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82421956866773 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (439529120641 / 20000000000000 : ℝ))
      (E := (cell13165 ⟨48, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82421956866773 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (439529120641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_49 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (10298527706171 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (137353099231 / 6250000000000 : ℝ))
      (E := (cell13165 ⟨49, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (10298527706171 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (137353099231 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_50 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (8235450970067 / 10000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197653644737 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨50, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (8235450970067 / 10000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197653644737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_51 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (20580205248089 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098828826689 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨51, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (20580205248089 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098828826689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_52 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82287155496243 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549415417373 / 25000000000000 : ℝ))
      (E := (cell13165 ⟨52, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82287155496243 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549415417373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_53 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (2570422287009 / 3125000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098832844869 / 50000000000000 : ℝ))
      (E := (cell13165 ⟨53, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (2570422287009 / 3125000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (1098832844869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_54 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82219894028591 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197669710567 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨54, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82219894028591 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197669710567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_55 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82186298001389 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197673728219 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨55, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82186298001389 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197673728219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_56 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (82152725075057 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549419434683 / 25000000000000 : ℝ))
      (E := (cell13165 ⟨56, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (82152725075057 / 100000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (549419434683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_57 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (20529793805527 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197681737933 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨57, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (20529793805527 / 25000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197681737933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_58 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (10260706051899 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197685780659 / 100000000000000 : ℝ))
      (E := (cell13165 ⟨58, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (10260706051899 / 12500000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (2197685780659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13165_59 : CellCertificate 13165 (874140434068359 / 10000000000000000 : ℝ) (398864124099739 / 250000000000000000 : ℝ) (161002868922533 / 5000000000000000 : ℝ)
    (cell13165 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · norm_num [cell13165]
  · have h := gap_lower (n := 13165) (a := (41026072313547 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (54942245079 / 2500000000000 : ℝ))
      (E := (cell13165 ⟨59, by decide⟩).energy) (xi := (161002868922533 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13165 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13165]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13165])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13165) (a := (41026072313547 / 50000000000000 : ℝ)) (b := (39098615779 / 25000000000000 : ℝ)) (q := (54942245079 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13165])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13165]

theorem cert13166_40 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41346332947207 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197502768193 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨40, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41346332947207 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197502768193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_41 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (3306349739859 / 4000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197506798013 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨41, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (3306349739859 / 4000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197506798013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_42 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (82624844599023 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (137344424903 / 6250000000000 : ℝ))
      (E := (cell13166 ⟨42, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (82624844599023 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (137344424903 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_43 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (82590969172573 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098757413539 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨43, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (82590969172573 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098757413539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_44 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41278558593893 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (439503764719 / 20000000000000 : ℝ))
      (E := (cell13166 ⟨44, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41278558593893 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (439503764719 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_45 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (82523288615473 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098761422597 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨45, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (82523288615473 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098761422597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_46 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (82489483426589 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197526890019 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨46, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (82489483426589 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197526890019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_47 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (20613925398059 / 25000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197530897043 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨47, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (20613925398059 / 25000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197530897043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_48 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (82421943083661 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197534922891 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨48, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (82421943083661 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197534922891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_49 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41194103936127 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197538906063 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨49, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41194103936127 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197538906063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_50 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (1647089918591 / 2000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197542961829 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨50, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (1647089918591 / 2000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197542961829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_51 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (3292832289089 / 4000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098773484621 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨51, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (3292832289089 / 4000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098773484621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_52 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (16457428347419 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (87902039367 / 4000000000000 : ℝ))
      (E := (cell13166 ⟨52, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (16457428347419 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (87902039367 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_53 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (1028168742889 / 1250000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (549388750821 / 25000000000000 : ℝ))
      (E := (cell13166 ⟨53, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (1028168742889 / 1250000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (549388750821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_54 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41109940140699 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098779511511 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨54, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41109940140699 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098779511511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_55 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (16437256852033 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197563039631 / 100000000000000 : ℝ))
      (E := (cell13166 ⟨55, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (16437256852033 / 20000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (2197563039631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_56 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41076355669899 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098783524573 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨56, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41076355669899 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098783524573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_57 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (82119161492809 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098785553293 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨57, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (82119161492809 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098785553293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_58 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (82085634691849 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098787544607 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨58, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (82085634691849 / 100000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098787544607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13166_59 : CellCertificate 13166 (874114360091977 / 10000000000000000 : ℝ) (1595335277919119 / 1000000000000000000 : ℝ) (321980723198187 / 10000000000000000 : ℝ)
    (cell13166 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · norm_num [cell13166]
  · have h := gap_lower (n := 13166) (a := (41026065454851 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098789555427 / 50000000000000 : ℝ))
      (E := (cell13166 ⟨59, by decide⟩).energy) (xi := (321980723198187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13166 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13166]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13166])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13166) (a := (41026065454851 / 50000000000000 : ℝ)) (b := (78191224561 / 50000000000000 : ℝ)) (q := (1098789555427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13166])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13166]

theorem cert13167_40 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82692652065243 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197392095923 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨40, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82692652065243 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197392095923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_41 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (4132936483667 / 5000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (274674515507 / 12500000000000 : ℝ))
      (E := (cell13167 ⟨41, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (4132936483667 / 5000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (274674515507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_42 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (516405192387 / 625000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (68668753839 / 3125000000000 : ℝ))
      (E := (cell13167 ⟨42, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (516405192387 / 625000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (68668753839 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_43 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (10323869420187 / 12500000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (549351037471 / 25000000000000 : ℝ))
      (E := (cell13167 ⟨43, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (10323869420187 / 12500000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (549351037471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_44 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (20639275845683 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (43948162897 / 2000000000000 : ℝ))
      (E := (cell13167 ⟨44, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (20639275845683 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (43948162897 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_45 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (16504654963287 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098706082473 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨45, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (16504654963287 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098706082473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_46 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82489469633563 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098708104157 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨46, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82489469633563 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098708104157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_47 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (41227843902609 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098710106963 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨47, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (41227843902609 / 50000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098710106963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_48 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (16484385860529 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197424238409 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨48, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (16484385860529 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197424238409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_49 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (20597048524309 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197428279263 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨49, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (20597048524309 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197428279263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_50 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (3294179286421 / 4000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098716137377 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨50, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (3294179286421 / 4000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098716137377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_51 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82320793464187 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (109871814047 / 5000000000000 : ℝ))
      (E := (cell13167 ⟨51, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82320793464187 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (109871814047 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_52 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82287127980041 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197440294691 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨52, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82287127980041 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197440294691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_53 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (20563371420011 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098722156333 / 50000000000000 : ℝ))
      (E := (cell13167 ⟨53, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (20563371420011 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (1098722156333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_54 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (16443973307259 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439489666263 / 20000000000000 : ℝ))
      (E := (cell13167 ⟨54, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (16443973307259 / 20000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439489666263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_55 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82186270521031 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (274681550753 / 12500000000000 : ℝ))
      (E := (cell13167 ⟨55, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82186270521031 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (274681550753 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_56 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (20538174401657 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439491282913 / 20000000000000 : ℝ))
      (E := (cell13167 ⟨56, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (20538174401657 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439491282913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_57 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82119147765599 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439492082377 / 20000000000000 : ℝ))
      (E := (cell13167 ⟨57, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82119147765599 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (439492082377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_58 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (82085620970593 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197464452823 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨58, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (82085620970593 / 100000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197464452823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13167_59 : CellCertificate 13167 (437044144952437 / 5000000000000000 : ℝ) (797607038928793 / 500000000000000000 : ℝ) (20122232028911 / 625000000000000 : ℝ)
    (cell13167 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · norm_num [cell13167]
  · have h := gap_lower (n := 13167) (a := (20513029298599 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197468473627 / 100000000000000 : ℝ))
      (E := (cell13167 ⟨59, by decide⟩).energy) (xi := (20122232028911 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13167 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13167]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13167])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13167) (a := (20513029298599 / 25000000000000 : ℝ)) (b := (156370436981 / 100000000000000 : ℝ)) (q := (2197468473627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13167])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13167]

theorem cert13168_40 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (3307705529527 / 4000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (17166261549 / 781250000000 : ℝ))
      (E := (cell13168 ⟨40, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (3307705529527 / 4000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (17166261549 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_41 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20664678963077 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (109864275237 / 5000000000000 : ℝ))
      (E := (cell13168 ⟨41, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20664678963077 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (109864275237 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_42 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41312408483459 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549322375479 / 25000000000000 : ℝ))
      (E := (cell13168 ⟨42, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41312408483459 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549322375479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_43 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82590941552521 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197293527379 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨43, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82590941552521 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197293527379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_44 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82557089579777 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (109864876041 / 5000000000000 : ℝ))
      (E := (cell13168 ⟨44, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82557089579777 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (109864876041 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_45 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (10315407627437 / 12500000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197301539437 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨45, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (10315407627437 / 12500000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197301539437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_46 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20622363960659 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197305581371 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨46, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20622363960659 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197305581371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_47 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (10306959252537 / 12500000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098654792799 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨47, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (10306959252537 / 12500000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098654792799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_48 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (3296876620949 / 4000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197313608739 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨48, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (3296876620949 / 4000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197313608739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_49 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82388180324313 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098658824149 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨49, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82388180324313 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098658824149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_50 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82354468393593 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (109866082127 / 5000000000000 : ℝ))
      (E := (cell13168 ⟨50, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82354468393593 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (109866082127 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_51 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41160389851621 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549331411881 / 25000000000000 : ℝ))
      (E := (cell13168 ⟨51, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41160389851621 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549331411881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_52 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (41143557112539 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098664830059 / 50000000000000 : ℝ))
      (E := (cell13168 ⟨52, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (41143557112539 / 50000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (1098664830059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_53 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82253471931059 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197333676981 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨53, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82253471931059 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197333676981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_54 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82219852793283 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (439467538913 / 20000000000000 : ℝ))
      (E := (cell13168 ⟨54, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82219852793283 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (439467538913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_55 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82186256783987 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (439468353651 / 20000000000000 : ℝ))
      (E := (cell13168 ⟨55, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82186256783987 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (439468353651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_56 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82152683875547 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197345775823 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨56, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82152683875547 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197345775823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_57 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (20529783510119 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197349772217 / 100000000000000 : ℝ))
      (E := (cell13168 ⟨57, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (20529783510119 / 25000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (2197349772217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_58 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (82085607251423 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (87894152491 / 4000000000000 : ℝ))
      (E := (cell13168 ⟨58, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (82085607251423 / 100000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (87894152491 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13168_59 : CellCertificate 13168 (109257777938273 / 1250000000000000 : ℝ) (1595092896210161 / 1000000000000000000 : ℝ) (321930705637267 / 10000000000000000 : ℝ)
    (cell13168 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · norm_num [cell13168]
  · have h := gap_lower (n := 13168) (a := (3282084139247 / 4000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549339458061 / 25000000000000 : ℝ))
      (E := (cell13168 ⟨59, by decide⟩).energy) (xi := (321930705637267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13168 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13168]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13168])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13168) (a := (3282084139247 / 4000000000000 : ℝ)) (b := (156358426691 / 100000000000000 : ℝ)) (q := (549339458061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13168])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13168]

theorem cert13169_40 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82692624413209 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197170856449 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨40, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82692624413209 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197170856449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_41 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82658702033377 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439434976251 / 20000000000000 : ℝ))
      (E := (cell13169 ⟨41, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82658702033377 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439434976251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_42 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (41312401577009 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (549294719203 / 25000000000000 : ℝ))
      (E := (cell13169 ⟨42, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (41312401577009 / 50000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (549294719203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_43 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (16518185549129 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439436580141 / 20000000000000 : ℝ))
      (E := (cell13169 ⟨43, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (16518185549129 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439436580141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_44 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82557075778921 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197186892623 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨44, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82557075778921 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197186892623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_45 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (16504649444931 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197190909761 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨45, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (16504649444931 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197190909761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_46 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (16497888410761 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197194950263 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨46, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (16497888410761 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197194950263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_47 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82455660237471 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197198953103 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨47, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82455660237471 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197198953103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_48 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (824219017469 / 1000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274650371863 / 12500000000000 : ℝ))
      (E := (cell13169 ⟨48, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (824219017469 / 1000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274650371863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_49 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (20597041638371 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197207013169 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨49, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (20597041638371 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197207013169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_50 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (16470890925751 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (549302751541 / 25000000000000 : ℝ))
      (E := (cell13169 ⟨50, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (16470890925751 / 20000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (549302751541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_51 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (8232076594439 / 10000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439443013799 / 20000000000000 : ℝ))
      (E := (cell13169 ⟨51, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (8232076594439 / 10000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (439443013799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_52 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82287100472207 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274652385057 / 12500000000000 : ℝ))
      (E := (cell13169 ⟨52, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82287100472207 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (274652385057 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_53 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (20563364546041 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098611548117 / 50000000000000 : ℝ))
      (E := (cell13169 ⟨53, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (20563364546041 / 25000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (1098611548117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_54 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (2055495976309 / 2500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197227112777 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨54, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (2055495976309 / 2500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197227112777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_55 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82186243049031 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197231126329 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨55, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82186243049031 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197231126329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_56 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (82152670146553 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (87889405317 / 4000000000000 : ℝ))
      (E := (cell13169 ⟨56, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (82152670146553 / 100000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (87889405317 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_57 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (16038890687 / 19531250000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197239187583 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨57, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (16038890687 / 19531250000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197239187583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_58 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (4104279676717 / 5000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197243167569 / 100000000000000 : ℝ))
      (E := (cell13169 ⟨58, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (4104279676717 / 5000000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (2197243167569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13169_59 : CellCertificate 13169 (874036160895039 / 10000000000000000 : ℝ) (1594971732972647 / 1000000000000000000 : ℝ) (160952851360647 / 5000000000000000 : ℝ)
    (cell13169 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · norm_num [cell13169]
  · have h := gap_lower (n := 13169) (a := (2051302244251 / 2500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (137327949169 / 6250000000000 : ℝ))
      (E := (cell13169 ⟨59, by decide⟩).energy) (xi := (160952851360647 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13169 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13169]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13169])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13169) (a := (2051302244251 / 2500000000000 : ℝ)) (b := (156346418251 / 100000000000000 : ℝ)) (q := (137327949169 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13169])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13169]

theorem cert13170_40 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41346305295173 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197060230453 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨40, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41346305295173 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197060230453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_41 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82658688216547 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197064253597 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨41, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82658688216547 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197064253597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_42 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82624789343217 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197068306377 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨42, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82624789343217 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197068306377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_43 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (20647728485217 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098536134931 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨43, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (20647728485217 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098536134931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_44 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82557061980163 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197076319141 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨44, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82557061980163 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197076319141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_45 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (10315404178989 / 12500000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (87883213393 / 4000000000000 : ℝ))
      (E := (cell13170 ⟨45, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (10315404178989 / 12500000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (87883213393 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_46 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82489428267071 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197084373919 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨46, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82489428267071 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197084373919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_47 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82455646456741 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197088375397 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨47, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82455646456741 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197088375397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_48 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (8242188797217 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197092395883 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨48, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (8242188797217 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197092395883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_49 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (20597038196187 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197096432879 / 100000000000000 : ℝ))
      (E := (cell13170 ⟨49, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (20597038196187 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (2197096432879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_50 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (8235444086601 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (274637553081 / 12500000000000 : ℝ))
      (E := (cell13170 ⟨50, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (8235444086601 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (274637553081 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_51 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (8232075218763 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549276106813 / 25000000000000 : ℝ))
      (E := (cell13170 ⟨51, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (8232075218763 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549276106813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_52 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82287086721427 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (274638562079 / 12500000000000 : ℝ))
      (E := (cell13170 ⟨52, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82287086721427 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (274638562079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_53 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (257042013873 / 312500000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549278127831 / 25000000000000 : ℝ))
      (E := (cell13170 ⟨53, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (257042013873 / 312500000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549278127831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_54 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (41109912656763 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549279131707 / 25000000000000 : ℝ))
      (E := (cell13170 ⟨54, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (41109912656763 / 50000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (549279131707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_55 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (20546557329041 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439424107877 / 20000000000000 : ℝ))
      (E := (cell13170 ⟨55, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (20546557329041 / 25000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439424107877 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_56 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82152656419647 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098562272517 / 50000000000000 : ℝ))
      (E := (cell13170 ⟨56, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82152656419647 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (1098562272517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_57 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (8211910659649 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (5492821349 / 250000000000 : ℝ))
      (E := (cell13170 ⟨57, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (8211910659649 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (5492821349 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_58 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (82085579819343 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (3433019653 / 156250000000 : ℝ))
      (E := (cell13170 ⟨58, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (82085579819343 / 100000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (3433019653 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13170_59 : CellCertificate 13170 (874010102070573 / 10000000000000000 : ℝ) (31897011762817 / 20000000000000000 : ℝ) (80470175928423 / 2500000000000000 : ℝ)
    (cell13170 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · norm_num [cell13170]
  · have h := gap_lower (n := 13170) (a := (8205207606099 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439427319249 / 20000000000000 : ℝ))
      (E := (cell13170 ⟨59, by decide⟩).energy) (xi := (80470175928423 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13170 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13170]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13170])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13170) (a := (8205207606099 / 10000000000000 : ℝ)) (b := (156334411663 / 100000000000000 : ℝ)) (q := (439427319249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13170])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13170]

theorem cert13171_40 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (5168287298099 / 6250000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196949659079 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨40, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (5168287298099 / 6250000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196949659079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_41 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82658674401819 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439390736117 / 20000000000000 : ℝ))
      (E := (cell13171 ⟨41, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82658674401819 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439390736117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_42 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (20656193883629 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274619709117 / 12500000000000 : ℝ))
      (E := (cell13171 ⟨42, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (20656193883629 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274619709117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_43 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (8259090013819 / 10000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098480846857 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨43, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (8259090013819 / 10000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098480846857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_44 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (5159815511469 / 6250000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196965741493 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨44, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (5159815511469 / 6250000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196965741493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_45 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41261609820633 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (549242438931 / 25000000000000 : ℝ))
      (E := (cell13171 ⟨45, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41261609820633 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (549242438931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_46 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82489414482433 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196973793411 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨46, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82489414482433 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196973793411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_47 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82455632678107 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274622224191 / 12500000000000 : ℝ))
      (E := (cell13171 ⟨47, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82455632678107 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (274622224191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_48 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41210937099767 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196981812699 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨48, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41210937099767 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196981812699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_49 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41194069509053 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098492924213 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨49, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41194069509053 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098492924213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_50 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82354427105357 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196989838973 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨50, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82354427105357 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196989838973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_51 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82320738432961 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (43939877989 / 2000000000000 : ℝ))
      (E := (cell13171 ⟨51, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82320738432961 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (43939877989 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_52 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41143536486369 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196997908649 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨52, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41143536486369 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2196997908649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_53 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41126715348323 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439400384451 / 20000000000000 : ℝ))
      (E := (cell13171 ⟨53, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41126715348323 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (439400384451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_54 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (41109905788391 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (27462574209 / 1250000000000 : ℝ))
      (E := (cell13171 ⟨54, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (41109905788391 / 50000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (27462574209 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_55 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (10273276948173 / 12500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098504974143 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨55, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (10273276948173 / 12500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098504974143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_56 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (20538160673707 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2197013952987 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨56, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (20538160673707 / 25000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2197013952987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_57 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (82119092877627 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098509002921 / 50000000000000 : ℝ))
      (E := (cell13171 ⟨57, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (82119092877627 / 100000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (1098509002921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_58 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (8208556610643 / 10000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2197021984117 / 100000000000000 : ℝ))
      (E := (cell13171 ⟨58, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (8208556610643 / 10000000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (2197021984117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13171_59 : CellCertificate 13171 (436992023515961 / 5000000000000000 : ℝ) (99670591356911 / 62500000000000000 : ℝ) (321855708613497 / 10000000000000000 : ℝ)
    (cell13171 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · norm_num [cell13171]
  · have h := gap_lower (n := 13171) (a := (10256507794253 / 12500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (219702606087 / 10000000000000 : ℝ))
      (E := (cell13171 ⟨59, by decide⟩).energy) (xi := (321855708613497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13171 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13171]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13171])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13171) (a := (10256507794253 / 12500000000000 : ℝ)) (b := (39080601731 / 25000000000000 : ℝ)) (q := (219702606087 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13171])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13171]

theorem cert13172_40 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82692582950923 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (439367816707 / 20000000000000 : ℝ))
      (E := (cell13172 ⟨40, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82692582950923 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (439367816707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_41 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (8265866058919 / 10000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (549210775851 / 25000000000000 : ℝ))
      (E := (cell13172 ⟨41, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (8265866058919 / 10000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (549210775851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_42 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (16524952345583 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098423576501 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨42, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (16524952345583 / 20000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098423576501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_43 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82590886337611 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196851172259 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨43, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82590886337611 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196851172259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_44 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41278517194471 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196855159677 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨44, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41278517194471 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196855159677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_45 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (20630801463179 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274607396557 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨45, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (20630801463179 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274607396557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_46 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82489400699891 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196863208737 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨46, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82489400699891 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196863208737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_47 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82455618901567 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098433603747 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨47, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82455618901567 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098433603747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_48 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82421860428993 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (219687128433 / 10000000000000 : ℝ))
      (E := (cell13172 ⟨48, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82421860428993 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (219687128433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_49 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41194062626779 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196875259809 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨49, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41194062626779 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196875259809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_50 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (20588603336699 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196879308161 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨50, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (20588603336699 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196879308161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_51 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (1286261323131 / 1562500000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (439376661687 / 20000000000000 : ℝ))
      (E := (cell13172 ⟨51, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (1286261323131 / 1562500000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (439376661687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_52 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82287059226139 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274610914563 / 12500000000000 : ℝ))
      (E := (cell13172 ⟨52, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82287059226139 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (274610914563 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_53 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (4112670847801 / 5000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196891329027 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨53, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (4112670847801 / 5000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196891329027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_54 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41109898921063 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098447700787 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨54, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41109898921063 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098447700787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_55 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (20546550464173 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196899412171 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨55, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (20546550464173 / 25000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196899412171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_56 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (1283634827689 / 1562500000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196903415949 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨56, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (1283634827689 / 1562500000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196903415949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_57 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82119079160849 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098453704369 / 50000000000000 : ℝ))
      (E := (cell13172 ⟨57, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82119079160849 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (1098453704369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_58 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (82085552395603 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (549227861343 / 25000000000000 : ℝ))
      (E := (cell13172 ⟨58, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (82085552395603 / 100000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (549227861343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13172_59 : CellCertificate 13172 (873957995778219 / 10000000000000000 : ℝ) (24915755526213 / 15625000000000000 : ℝ) (64366143483949 / 2000000000000000 : ℝ)
    (cell13172 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · norm_num [cell13172]
  · have h := gap_lower (n := 13172) (a := (41026024324571 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196915462103 / 100000000000000 : ℝ))
      (E := (cell13172 ⟨59, by decide⟩).energy) (xi := (64366143483949 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13172 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13172]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13172])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13172) (a := (41026024324571 / 50000000000000 : ℝ)) (b := (39077601009 / 25000000000000 : ℝ)) (q := (2196915462103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13172])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13172]

theorem cert13173_40 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82692569134363 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439345712523 / 20000000000000 : ℝ))
      (E := (cell13173 ⟨40, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82692569134363 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439345712523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_41 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82658646778661 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196732580871 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨41, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82658646778661 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196732580871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_42 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (20656186980853 / 25000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196736628903 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨42, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (20656186980853 / 25000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196736628903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_43 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82590872539129 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (27459258083 / 1250000000000 : ℝ))
      (E := (cell13173 ⟨43, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82590872539129 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (27459258083 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_44 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (20639255149119 / 25000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439348926517 / 20000000000000 : ℝ))
      (E := (cell13173 ⟨44, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (20639255149119 / 25000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439348926517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_45 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (41261596033131 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439349728787 / 20000000000000 : ℝ))
      (E := (cell13173 ⟨45, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (41261596033131 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (439349728787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_46 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82489386919443 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098376339417 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨46, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82489386919443 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098376339417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_47 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (41227802563561 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098378338127 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨47, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (41227802563561 / 50000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098378338127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_48 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (1287841354071 / 1562500000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196760692821 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨48, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (1287841354071 / 1562500000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196760692821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_49 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82388111491101 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549191181509 / 25000000000000 : ℝ))
      (E := (cell13173 ⟨49, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82388111491101 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549191181509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_50 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82354399590327 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219676877319 / 10000000000000 : ℝ))
      (E := (cell13173 ⟨50, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82354399590327 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (219676877319 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_51 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82320710929897 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196772772313 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨51, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82320710929897 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196772772313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_52 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (8228704548163 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549194194819 / 25000000000000 : ℝ))
      (E := (cell13173 ⟨52, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (8228704548163 / 10000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (549194194819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_53 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (20563350804371 / 25000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196780790739 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨53, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (20563350804371 / 25000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196780790739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_54 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82219784109557 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196784862273 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨54, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82219784109557 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196784862273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_55 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82186188130087 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098394435951 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨55, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82186188130087 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098394435951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_56 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82152615251449 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196792874759 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨56, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82152615251449 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196792874759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_57 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (82119065446157 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098398462931 / 50000000000000 : ℝ))
      (E := (cell13173 ⟨57, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (82119065446157 / 100000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (1098398462931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_58 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (4104276934343 / 5000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (87872036099 / 4000000000000 : ℝ))
      (E := (cell13173 ⟨58, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (4104276934343 / 5000000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (87872036099 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13173_59 : CellCertificate 13173 (4369659741543 / 50000000000000 : ℝ) (398621816009457 / 250000000000000000 : ℝ) (321805730131471 / 10000000000000000 : ℝ)
    (cell13173 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · norm_num [cell13173]
  · have h := gap_lower (n := 13173) (a := (10256504368293 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196804918421 / 100000000000000 : ℝ))
      (E := (cell13173 ⟨59, by decide⟩).energy) (xi := (321805730131471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13173 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13173]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13173])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13173) (a := (10256504368293 / 12500000000000 : ℝ)) (b := (39074600749 / 25000000000000 : ℝ)) (q := (2196804918421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13173])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13173]

theorem cert13174_40 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82692555319903 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196618037527 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨40, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82692555319903 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196618037527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_41 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82658632970231 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (549155513543 / 25000000000000 : ℝ))
      (E := (cell13174 ⟨41, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82658632970231 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (549155513543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_42 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82624734121007 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098313050319 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨42, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82624734121007 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098313050319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_43 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (16518171748549 / 20000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439326023371 / 20000000000000 : ℝ))
      (E := (cell13174 ⟨43, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (16518171748549 / 20000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (439326023371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_44 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (20639251701527 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098317050663 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨44, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (20639251701527 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098317050663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_45 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (5157698642619 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196638170159 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨45, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (5157698642619 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196638170159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_46 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82489373141091 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (4290316689 / 195312500000 : ℝ))
      (E := (cell13174 ⟨46, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82489373141091 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (4290316689 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_47 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (8245559135477 / 10000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (219664619981 / 10000000000000 : ℝ))
      (E := (cell13174 ⟨47, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (8245559135477 / 10000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (219664619981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_48 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (20605458223547 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196650215111 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨48, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (20605458223547 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196650215111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_49 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (5149256108171 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196654247107 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨49, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (5149256108171 / 6250000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196654247107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_50 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (20588596458987 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196658234061 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨50, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (20588596458987 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196658234061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_51 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (164641394363 / 200000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (68645694751 / 3125000000000 : ℝ))
      (E := (cell13174 ⟨51, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (164641394363 / 200000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (68645694751 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_52 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (8228703173921 / 10000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (549166574241 / 25000000000000 : ℝ))
      (E := (cell13174 ⟨52, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (8228703173921 / 10000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (549166574241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_53 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (20563347370259 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (34322973553 / 1562500000000 : ℝ))
      (E := (cell13174 ⟨53, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (20563347370259 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (34322973553 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_54 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (20554942594769 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (68646072463 / 3125000000000 : ℝ))
      (E := (cell13174 ⟨54, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (20554942594769 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (68646072463 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_55 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82186174405569 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196678327477 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨55, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82186174405569 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196678327477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_56 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82152601532889 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196682329413 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨56, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82152601532889 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196682329413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_57 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (82119051733549 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098343189821 / 50000000000000 : ℝ))
      (E := (cell13174 ⟨57, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (82119051733549 / 100000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (1098343189821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_58 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (410427624901 / 500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196690414641 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨58, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (410427624901 / 500000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196690414641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

theorem cert13174_59 : CellCertificate 13174 (873905904622199 / 10000000000000000 : ℝ) (1594366192786973 / 1000000000000000000 : ℝ) (321780746747711 / 10000000000000000 : ℝ)
    (cell13174 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · norm_num [cell13174]
  · have h := gap_lower (n := 13174) (a := (20513005311407 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196694429827 / 100000000000000 : ℝ))
      (E := (cell13174 ⟨59, by decide⟩).energy) (xi := (321780746747711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13174 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13174]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13174])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13174) (a := (20513005311407 / 25000000000000 : ℝ)) (b := (31257280761 / 20000000000000 : ℝ)) (q := (2196694429827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13174])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13174]

end BstLean.Part268
