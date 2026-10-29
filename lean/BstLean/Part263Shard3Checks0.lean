import BstLean.Part263Shard3Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12300_0 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (5255139949401 / 6250000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304109469251 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨0, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (5255139949401 / 6250000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304109469251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_1 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (42023566481433 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460822689053 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨1, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (42023566481433 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460822689053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_2 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (84012051855533 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576029356311 / 25000000000000 : ℝ))
      (E := (cell12300 ⟨2, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (84012051855533 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576029356311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_3 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41988497915751 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304121418847 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨3, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41988497915751 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304121418847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_4 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (16788392970811 / 20000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152062717737 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨4, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (16788392970811 / 20000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152062717737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_5 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83906958886669 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304129426373 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨5, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83906958886669 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304129426373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_6 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20967994473253 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152066700177 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨6, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20967994473253 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152066700177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_7 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83837021836943 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304137423899 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨7, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83837021836943 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304137423899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_8 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (5237630667657 / 6250000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304141389463 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨8, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (5237630667657 / 6250000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304141389463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_9 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83767184393959 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (230414536299 / 10000000000000 : ℝ))
      (E := (cell12300 ⟨9, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83767184393959 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (230414536299 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_10 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83732302935711 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460829870453 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨10, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83732302935711 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460829870453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_11 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83697446272379 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304153364821 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨11, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83697446272379 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304153364821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_12 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41831307184381 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304157349887 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨12, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41831307184381 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304157349887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_13 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20906951797461 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304161372493 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨13, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20906951797461 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304161372493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_14 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20898256175197 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304165323229 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨14, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20898256175197 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304165323229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_15 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41779133433471 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152084662361 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨15, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41779133433471 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152084662361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_16 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41761766826917 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304173325113 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨16, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41761766826917 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304173325113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_17 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83488825027169 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304177330371 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨17, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83488825027169 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304177330371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_18 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83454140952833 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460836269243 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨18, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83454140952833 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460836269243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_19 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (83419481396889 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (230418531991 / 10000000000000 : ℝ))
      (E := (cell12300 ⟨19, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (83419481396889 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (230418531991 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12301_0 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (16816444612217 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303966326719 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨0, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (16816444612217 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303966326719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_1 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (84047117169813 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303970300773 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨1, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (84047117169813 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303970300773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_2 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (84012036398281 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303974279591 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨2, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (84012036398281 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303974279591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_3 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (3359079228383 / 4000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (35999660513 / 1562500000000 : ℝ))
      (E := (cell12301 ⟨3, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (3359079228383 / 4000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (35999660513 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_4 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41970975033489 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (575995572473 / 25000000000000 : ℝ))
      (E := (cell12301 ⟨4, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41970975033489 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (575995572473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_5 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83906944433967 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303986282021 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨5, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83906944433967 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303986282021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_6 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (20967990943553 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1151995129013 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨6, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (20967990943553 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1151995129013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_7 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83837008051573 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1151997113229 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨7, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83837008051573 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1151997113229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_8 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41901038615051 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303998253563 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨8, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41901038615051 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2303998253563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_9 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41883585637019 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304002231493 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨9, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41883585637019 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304002231493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_10 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (2616634067119 / 3125000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152003112981 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨10, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (2616634067119 / 3125000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152003112981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_11 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83697433816029 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (4608020489 / 200000000000 : ℝ))
      (E := (cell12301 ⟨11, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83697433816029 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (4608020489 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_12 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83662602243497 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304014236337 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨12, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83662602243497 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304014236337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_13 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83627795395197 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144001138027 / 6250000000000 : ℝ))
      (E := (cell12301 ⟨13, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83627795395197 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144001138027 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_14 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (16718602647259 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152011112793 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨14, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (16718602647259 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152011112793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_15 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83558255732139 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576006544523 / 25000000000000 : ℝ))
      (E := (cell12301 ⟨15, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83558255732139 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576006544523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_16 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (163131880563 / 195312500000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152015094189 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨16, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (163131880563 / 195312500000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152015094189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_17 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (20872203637589 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (288004275539 / 12500000000000 : ℝ))
      (E := (cell12301 ⟨17, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (20872203637589 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (288004275539 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_18 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83454130804323 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576009543357 / 25000000000000 : ℝ))
      (E := (cell12301 ⟨18, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83454130804323 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576009543357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_19 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (83419471576221 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144002634959 / 6250000000000 : ℝ))
      (E := (cell12301 ⟨19, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (83419471576221 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144002634959 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12302_0 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (4204110346719 / 5000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (57595580917 / 2500000000000 : ℝ))
      (E := (cell12302 ⟨0, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (4204110346719 / 5000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (57595580917 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_1 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (5252943836209 / 6250000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151913604421 / 50000000000000 : ℝ))
      (E := (cell12302 ⟨1, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (5252943836209 / 6250000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151913604421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_2 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (84012020943571 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303831244381 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨2, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (84012020943571 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303831244381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_3 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83976965590147 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303835237349 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨3, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83976965590147 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303835237349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_4 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41970967641179 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303839197071 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨4, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41970967641179 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303839197071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_5 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (262209156199 / 312500000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (71995099703 / 3125000000000 : ℝ))
      (E := (cell12302 ⟨5, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (262209156199 / 312500000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (71995099703 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_6 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (16774389931557 / 20000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303847168593 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨6, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (16774389931557 / 20000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303847168593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_7 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41918497134267 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303851197841 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨7, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41918497134267 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303851197841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_8 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (4190103188999 / 5000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (575963792673 / 25000000000000 : ℝ))
      (E := (cell12302 ⟨8, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (4190103188999 / 5000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (575963792673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_9 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83767158156363 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (230385915309 / 10000000000000 : ℝ))
      (E := (cell12302 ⟨9, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83767158156363 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (230385915309 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_10 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (1308316833783 / 1562500000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303863152819 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨10, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (1308316833783 / 1562500000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303863152819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_11 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83697421361843 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (460773435481 / 20000000000000 : ℝ))
      (E := (cell12302 ⟨11, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83697421361843 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (460773435481 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_12 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41831295060177 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (143991944877 / 6250000000000 : ℝ))
      (E := (cell12302 ⟨12, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41831295060177 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (143991944877 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_13 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (10453472950329 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (11519375779 / 500000000000 : ℝ))
      (E := (cell12302 ⟨13, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (10453472950329 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (11519375779 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_14 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41796500886921 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303879123271 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨14, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41796500886921 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303879123271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_15 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41779122299667 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (71996348221 / 3125000000000 : ℝ))
      (E := (cell12302 ⟨15, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41779122299667 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (71996348221 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_16 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (20880878011159 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151943552599 / 50000000000000 : ℝ))
      (E := (cell12302 ⟨16, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (20880878011159 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151943552599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_17 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83488804075459 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303891131877 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨17, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83488804075459 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303891131877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_18 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (10431765082211 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303895112519 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨18, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (10431765082211 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303895112519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_19 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (83419461757387 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (460779822149 / 20000000000000 : ℝ))
      (E := (cell12302 ⟨19, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (83419461757387 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (460779822149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12303_0 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (840821908103 / 1000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460736051381 / 20000000000000 : ℝ))
      (E := (cell12303 ⟨0, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (840821908103 / 1000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460736051381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_1 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (42023542795729 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460736845453 / 20000000000000 : ℝ))
      (E := (cell12303 ⟨1, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (42023542795729 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460736845453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_2 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (84012005491401 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151844101993 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨2, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (84012005491401 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151844101993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_3 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41988475236609 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (575923049181 / 25000000000000 : ℝ))
      (E := (cell12303 ⟨3, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41988475236609 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (575923049181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_4 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41970960250097 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (18429569719 / 800000000000 : ℝ))
      (E := (cell12303 ⟨4, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41970960250097 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (18429569719 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_5 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83906915535807 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303700209687 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨5, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83906915535807 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303700209687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_6 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83871935543731 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (575926047491 / 25000000000000 : ℝ))
      (E := (cell12303 ⟨6, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83871935543731 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (575926047491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_7 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41918490243913 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460741632851 / 20000000000000 : ℝ))
      (E := (cell12303 ⟨7, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41918490243913 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460741632851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_8 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83802050332147 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460742439761 / 20000000000000 : ℝ))
      (E := (cell12303 ⟨8, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83802050332147 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460742439761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_9 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (10470893130117 / 12500000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151858092881 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨9, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (10470893130117 / 12500000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151858092881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_10 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41866132289311 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303720190839 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨10, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41866132289311 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303720190839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_11 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83697408909821 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303724163539 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨11, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83697408909821 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303724163539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_12 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41831288999667 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303728169119 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨12, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41831288999667 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303728169119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_13 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83627771812147 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230373215653 / 10000000000000 : ℝ))
      (E := (cell12303 ⟨13, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83627771812147 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230373215653 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_14 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20898247578357 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (3599587707 / 156250000000 : ℝ))
      (E := (cell12303 ⟨14, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20898247578357 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (3599587707 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_15 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41779116734263 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151870051713 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨15, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41779116734263 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151870051713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_16 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83523501242973 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (57593603343 / 2500000000000 : ℝ))
      (E := (cell12303 ⟨16, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83523501242973 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (57593603343 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_17 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83488793602477 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151874056533 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨17, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83488793602477 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151874056533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_18 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83454110512927 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (23037521053 / 1000000000000 : ℝ))
      (E := (cell12303 ⟨18, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83454110512927 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (23037521053 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_19 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (83419451940387 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (23037561159 / 1000000000000 : ℝ))
      (E := (cell12303 ⟨19, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (83419451940387 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (23037561159 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12304_0 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (21020543672211 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575884332407 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨0, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (21020543672211 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575884332407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_1 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (42023534903077 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575885324563 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨1, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (42023534903077 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575885324563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_2 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (84011990041771 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303545331851 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨2, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (84011990041771 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303545331851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_3 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41988467679393 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151774662237 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨3, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41988467679393 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151774662237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_4 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (16788381144097 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575888321361 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨4, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (16788381144097 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575888321361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_5 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (20976725272587 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303557281709 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨5, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (20976725272587 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303557281709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_6 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (5241995089503 / 6250000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303561264233 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨6, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (5241995089503 / 6250000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303561264233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_7 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (10479620838681 / 12500000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (460713048313 / 20000000000000 : ℝ))
      (E := (cell12304 ⟨7, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (10479620838681 / 12500000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (460713048313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_8 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83802036886603 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575892319987 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨8, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83802036886603 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575892319987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_9 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (16753426385551 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (230357327153 / 10000000000000 : ℝ))
      (E := (cell12304 ⟨9, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (16753426385551 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (230357327153 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_10 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (10466531474667 / 12500000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (115178861201 / 5000000000000 : ℝ))
      (E := (cell12304 ⟨10, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (10466531474667 / 12500000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (115178861201 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_11 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41848698229981 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (17996728601 / 781250000000 : ℝ))
      (E := (cell12304 ⟨11, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41848698229981 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (17996728601 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_12 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (16732513176087 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303585215453 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨12, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (16732513176087 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303585215453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_13 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41813880011871 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151794605311 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨13, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41813880011871 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151794605311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_14 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83592978855053 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (460718639023 / 20000000000000 : ℝ))
      (E := (cell12304 ⟨14, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83592978855053 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (460718639023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_15 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83558222339717 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303597233511 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨15, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83558222339717 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303597233511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_16 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41761745221633 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303601215801 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨16, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41761745221633 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303601215801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_17 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (8348878313141 / 10000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151802603023 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨17, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (8348878313141 / 10000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151802603023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_18 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (83454100370039 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575902302491 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨18, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (83454100370039 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575902302491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_19 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41709721062609 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (460722634963 / 20000000000000 : ℝ))
      (E := (cell12304 ⟨19, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41709721062609 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (460722634963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12305_0 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (21020539642503 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303394454851 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨0, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (21020539642503 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303394454851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_1 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (84047054023431 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303398479597 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨1, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (84047054023431 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303398479597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_2 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (84011974594681 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460680490907 / 20000000000000 : ℝ))
      (E := (cell12305 ⟨2, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (84011974594681 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460680490907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_3 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (20994230061713 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151703223543 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨3, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (20994230061713 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151703223543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_4 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (327898011497 / 390625000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151705233321 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨4, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (327898011497 / 390625000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151705233321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_5 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (83906886647303 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303414464449 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨5, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (83906886647303 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303414464449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_6 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (83871907322737 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303418449311 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨6, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (83871907322737 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303418449311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_7 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (419184764667 / 500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303422429773 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨7, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (419184764667 / 500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303422429773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_8 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41901011721673 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (18427411313 / 800000000000 : ℝ))
      (E := (cell12305 ⟨8, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41901011721673 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (18427411313 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_9 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (83767118816821 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303430410397 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨9, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (83767118816821 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303430410397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_10 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41866119509127 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303434426373 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨10, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41866119509127 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303434426373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_11 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41848692006133 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303438411549 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨11, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41848692006133 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303438411549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_12 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41831276881829 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303442373133 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨12, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41831276881829 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303442373133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_13 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41813874118709 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (46068927523 / 2000000000000 : ℝ))
      (E := (cell12305 ⟨13, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41813874118709 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (46068927523 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_14 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (20898241849679 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151725184639 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨14, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (20898241849679 / 25000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151725184639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_15 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (10444776401613 / 12500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151727179487 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨15, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (10444776401613 / 12500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151727179487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_16 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41761739822757 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460691670289 / 20000000000000 : ℝ))
      (E := (cell12305 ⟨16, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41761739822757 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460691670289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_17 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41744386331129 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460692470531 / 20000000000000 : ℝ))
      (E := (cell12305 ⟨17, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41744386331129 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460692470531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_18 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (3338163609161 / 4000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303466368321 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨18, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (3338163609161 / 4000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303466368321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_19 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41709716155941 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151735172851 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨19, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41709716155941 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151735172851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12306_0 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (21020535613451 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151625845171 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨0, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (21020535613451 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151625845171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_1 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (8404703824329 / 10000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230325571351 / 10000000000000 : ℝ))
      (E := (cell12306 ⟨1, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (8404703824329 / 10000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230325571351 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_2 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (84011959150129 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303259687669 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨2, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (84011959150129 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303259687669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_3 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41988452568707 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151631840119 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨3, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41988452568707 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151631840119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_4 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41970938084217 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (17994278911 / 781250000000 : ℝ))
      (E := (cell12306 ⟨4, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41970938084217 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (17994278911 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_5 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (8390687220667 / 10000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (92130868001 / 4000000000000 : ℝ))
      (E := (cell12306 ⟨5, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (8390687220667 / 10000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (92130868001 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_6 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83871893215797 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230327568729 / 10000000000000 : ℝ))
      (E := (cell12306 ⟨6, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83871893215797 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230327568729 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_7 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (130995217437 / 156250000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303279670951 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨7, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (130995217437 / 156250000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303279670951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_8 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83802010002377 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303283659291 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨8, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83802010002377 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303283659291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_9 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83767105708131 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151643830173 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨9, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83767105708131 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151643830173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_10 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (2616632070043 / 3125000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230329162389 / 10000000000000 : ℝ))
      (E := (cell12306 ⟨10, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (2616632070043 / 3125000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230329162389 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_11 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20924342891683 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575823903851 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨11, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20924342891683 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575823903851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_12 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83662541649001 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303299642163 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨12, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83662541649001 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303299642163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_13 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20906934113293 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575825898761 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨13, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20906934113293 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575825898761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_14 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83592955944417 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (287913449609 / 12500000000000 : ℝ))
      (E := (cell12306 ⟨14, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83592955944417 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (287913449609 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_15 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83558200088087 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460662319211 / 20000000000000 : ℝ))
      (E := (cell12306 ⟨15, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83558200088087 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460662319211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_16 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83523468849717 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303315598797 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨16, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83523468849717 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303315598797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_17 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (83488762195019 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (115165980553 / 5000000000000 : ℝ))
      (E := (cell12306 ⟨17, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (83488762195019 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (115165980553 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_18 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20863520022471 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575830895093 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨18, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20863520022471 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575830895093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_19 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41709711250189 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303327570349 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨19, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41709711250189 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303327570349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12307_0 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (84082126340217 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151554518053 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨0, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (84082126340217 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151554518053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_1 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (1313234726027 / 1562500000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460622599999 / 20000000000000 : ℝ))
      (E := (cell12307 ⟨1, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (1313234726027 / 1562500000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460622599999 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_2 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (21002985927029 / 25000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460623406251 / 20000000000000 : ℝ))
      (E := (cell12307 ⟨2, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (21002985927029 / 25000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460623406251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_3 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83976890030473 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575780255983 / 25000000000000 : ℝ))
      (E := (cell12307 ⟨3, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83976890030473 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575780255983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_4 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (8394186139609 / 10000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (143945311709 / 6250000000000 : ℝ))
      (E := (cell12307 ⟨4, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (8394186139609 / 10000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (143945311709 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_5 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83906857768449 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303128988437 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨5, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83906857768449 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303128988437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_6 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41935939555613 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151566489087 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨6, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41935939555613 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151566489087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_7 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83836925388289 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303136965097 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨7, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83836925388289 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303136965097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_8 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41900998281847 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151570478747 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨8, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41900998281847 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151570478747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_9 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83767092601687 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575786240849 / 25000000000000 : ℝ))
      (E := (cell12307 ⟨9, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83767092601687 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575786240849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_10 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41866106733351 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151574466289 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨10, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41866106733351 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151574466289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_11 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83697359123359 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (57578823263 / 2500000000000 : ℝ))
      (E := (cell12307 ⟨11, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83697359123359 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (57578823263 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_12 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (5228908096029 / 6250000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460631381289 / 20000000000000 : ℝ))
      (E := (cell12307 ⟨12, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (5228908096029 / 6250000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460631381289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_13 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (16725544934201 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303160925379 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨13, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (16725544934201 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303160925379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_14 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (16718588898431 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303164935997 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨14, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (16718588898431 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303164935997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_15 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (83558188965267 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303168886633 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨15, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (83558188965267 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303168886633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_16 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (668187664447 / 800000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303172899713 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨16, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (668187664447 / 800000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303172899713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_17 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41744375864847 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303176923097 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨17, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41744375864847 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303176923097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_18 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41727034976307 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (287897613039 / 12500000000000 : ℝ))
      (E := (cell12307 ⟨18, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41727034976307 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (287897613039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_19 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (16683882538141 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303184906973 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨19, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (16683882538141 / 20000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303184906973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12308_0 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (84082110229253 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460593275321 / 20000000000000 : ℝ))
      (E := (cell12308 ⟨0, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (84082110229253 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460593275321 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_1 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (84047006690747 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2302970396841 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨1, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (84047006690747 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2302970396841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_2 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (525074551679 / 625000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (17991987263 / 781250000000 : ℝ))
      (E := (cell12308 ⟨2, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (525074551679 / 625000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (17991987263 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_3 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83976874926027 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (575744590623 / 25000000000000 : ℝ))
      (E := (cell12308 ⟨3, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83976874926027 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (575744590623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_4 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83941846626199 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2302982384713 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨4, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83941846626199 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2302982384713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_5 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (524417770829 / 625000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2302986387573 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨5, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (524417770829 / 625000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2302986387573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_6 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41935932504513 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (230299037987 / 10000000000000 : ℝ))
      (E := (cell12308 ⟨6, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41935932504513 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (230299037987 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_7 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (3353476464769 / 4000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (575748592537 / 25000000000000 : ℝ))
      (E := (cell12308 ⟨7, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (3353476464769 / 4000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (575748592537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_8 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (327351496591 / 390625000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2302998366691 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨8, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (327351496591 / 390625000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2302998366691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_9 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41883539748743 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303002319551 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨9, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41883539748743 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303002319551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_10 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (8373220069423 / 10000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303006352439 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨10, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (8373220069423 / 10000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303006352439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_11 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (20924336670537 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303010298871 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨11, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (20924336670537 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303010298871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_12 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41831258713023 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303014340129 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨12, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41831258713023 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303014340129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_13 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (20906928222729 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151509154541 / 50000000000000 : ℝ))
      (E := (cell12308 ⟨13, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (20906928222729 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151509154541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_14 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83592933041929 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (575755582139 / 25000000000000 : ℝ))
      (E := (cell12308 ⟨14, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83592933041929 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (575755582139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_15 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41779088922221 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303026288833 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨15, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41779088922221 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303026288833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_16 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (20880861815997 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151515156169 / 50000000000000 : ℝ))
      (E := (cell12308 ⟨16, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (20880861815997 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151515156169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_17 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41744370633141 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460606857753 / 20000000000000 : ℝ))
      (E := (cell12308 ⟨17, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41744370633141 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460606857753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_18 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (83454059817217 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (575759570487 / 25000000000000 : ℝ))
      (E := (cell12308 ⟨18, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (83454059817217 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (575759570487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_19 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41709701441431 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303042297361 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨19, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41709701441431 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303042297361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12309_0 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (8408209412091 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302823885147 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨0, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (8408209412091 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302823885147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_1 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (10505873864793 / 12500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (115141392313 / 5000000000000 : ℝ))
      (E := (cell12309 ⟨1, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (10505873864793 / 12500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (115141392313 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_2 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (84011912831701 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302831818527 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨2, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (84011912831701 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302831818527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_3 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (20994214956019 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575708952899 / 25000000000000 : ℝ))
      (E := (cell12309 ⟨3, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (20994214956019 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575708952899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_4 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83941831858761 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287854979357 / 12500000000000 : ℝ))
      (E := (cell12309 ⟨4, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83941831858761 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287854979357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_5 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83906828899241 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575710959887 / 25000000000000 : ℝ))
      (E := (cell12309 ⟨5, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83906828899241 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575710959887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_6 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41935925454597 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287855979309 / 12500000000000 : ℝ))
      (E := (cell12309 ⟨6, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41935925454597 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287855979309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_7 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83836897852489 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (230285182817 / 10000000000000 : ℝ))
      (E := (cell12309 ⟨7, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83836897852489 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (230285182817 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_8 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (16760393938637 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (92114233157 / 4000000000000 : ℝ))
      (E := (cell12309 ⟨8, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (16760393938637 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (92114233157 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_9 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (8376706639553 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575714946697 / 25000000000000 : ℝ))
      (E := (cell12309 ⟨9, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (8376706639553 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575714946697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_10 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (2093304698099 / 2500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575715941867 / 25000000000000 : ℝ))
      (E := (cell12309 ⟨10, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (2093304698099 / 2500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575715941867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_11 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83697334243097 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302867778487 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨11, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83697334243097 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302867778487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_12 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (20915626329437 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460574353813 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨12, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (20915626329437 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460574353813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_13 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (10453462639113 / 12500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151437873077 / 50000000000000 : ℝ))
      (E := (cell12309 ⟨13, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (10453462639113 / 12500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (1151437873077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_14 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (4179646079687 / 5000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (46057595491 / 2000000000000 : ℝ))
      (E := (cell12309 ⟨14, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (4179646079687 / 5000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (46057595491 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_15 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83558166725611 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460576748907 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨15, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83558166725611 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460576748907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_16 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (83523436474053 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575721930097 / 25000000000000 : ℝ))
      (E := (cell12309 ⟨16, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (83523436474053 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575721930097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_17 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41744365402391 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302891766233 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨17, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41744365402391 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302891766233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_18 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (8345404968369 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460579142657 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨18, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (8345404968369 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460579142657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_19 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (1668387861537 / 2000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287862467689 / 12500000000000 : ℝ))
      (E := (cell12309 ⟨19, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (1668387861537 / 2000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287862467689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12310_0 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (21020519503797 / 25000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575670347107 / 25000000000000 : ℝ))
      (E := (cell12310 ⟨0, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (21020519503797 / 25000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575670347107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_1 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (2101174378713 / 2500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302685406047 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨1, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (2101174378713 / 2500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302685406047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_2 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (42005948698649 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (287836172231 / 12500000000000 : ℝ))
      (E := (cell12310 ⟨2, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (42005948698649 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (287836172231 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_3 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83976844724619 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (143918335703 / 6250000000000 : ℝ))
      (E := (cell12310 ⟨3, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83976844724619 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (143918335703 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_4 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (3357672683751 / 4000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302697337773 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨4, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (3357672683751 / 4000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302697337773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_5 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83906814468253 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (460540268873 / 20000000000000 : ℝ))
      (E := (cell12310 ⟨5, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83906814468253 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (460540268873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_6 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83871836811731 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302705341983 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨6, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83871836811731 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302705341983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_7 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83836884088079 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302709339167 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨7, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83836884088079 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302709339167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_8 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41900978130679 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302713344201 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨8, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41900978130679 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302713344201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_9 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (10470881661977 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (460543461427 / 20000000000000 : ℝ))
      (E := (cell12310 ⟨9, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (10470881661977 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (460543461427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_10 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83732175155891 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (92108851747 / 4000000000000 : ℝ))
      (E := (cell12310 ⟨10, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83732175155891 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (92108851747 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_11 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41848660903103 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151362655671 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨11, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41848660903103 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151362655671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_12 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (5228905825723 / 6250000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302729309359 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨12, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (5228905825723 / 6250000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302729309359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_13 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (8362768933697 / 10000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (143920830917 / 6250000000000 : ℝ))
      (E := (cell12310 ⟨13, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (8362768933697 / 10000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (143920830917 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_14 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83592910147587 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151368636991 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨14, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83592910147587 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151368636991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_15 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (3342326224351 / 4000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302741311861 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨15, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (3342326224351 / 4000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302741311861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_16 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (10440428210759 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151372649147 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨16, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (10440428210759 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151372649147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_17 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41744360172597 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302749297337 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨17, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41744360172597 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302749297337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_18 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (16690807910407 / 20000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (35980519633 / 1562500000000 : ℝ))
      (E := (cell12310 ⟨18, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (16690807910407 / 20000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (35980519633 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_19 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (83419383272667 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (287844654929 / 12500000000000 : ℝ))
      (E := (cell12310 ⟨19, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (83419383272667 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (287844654929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12311_0 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (16816412382417 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575634750497 / 25000000000000 : ℝ))
      (E := (cell12311 ⟨0, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (16816412382417 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575634750497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_1 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (84046959381273 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (230254301841 / 10000000000000 : ℝ))
      (E := (cell12311 ⟨1, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (84046959381273 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (230254301841 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_2 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (84011881965431 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575636747453 / 25000000000000 : ℝ))
      (E := (cell12311 ⟨2, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (84011881965431 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575636747453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_3 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (16795365925531 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302550983611 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨3, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (16795365925531 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302550983611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_4 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (83941802331241 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (230255495133 / 10000000000000 : ℝ))
      (E := (cell12311 ⟨4, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (83941802331241 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (230255495133 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_5 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41953400019837 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302558959911 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨5, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41953400019837 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302558959911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_6 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (16774364543327 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (287820370039 / 12500000000000 : ℝ))
      (E := (cell12311 ⟨6, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (16774364543327 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (287820370039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_7 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (16767374065199 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302566961073 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨7, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (16767374065199 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302566961073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_8 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (16760388566363 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575642742619 / 25000000000000 : ℝ))
      (E := (cell12311 ⟨8, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (16760388566363 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575642742619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_9 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41883520099173 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (287821867321 / 12500000000000 : ℝ))
      (E := (cell12311 ⟨9, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41883520099173 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (287821867321 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_10 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (10466520298753 / 12500000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151289465529 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨10, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (10466520298753 / 12500000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151289465529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_11 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41848654685737 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302582897439 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨11, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41848654685737 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302582897439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_12 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41831240553753 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302586902959 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨12, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41831240553753 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302586902959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_13 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (10453459695389 / 12500000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302590896563 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨13, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (10453459695389 / 12500000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302590896563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_14 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (20898224675867 / 25000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302594884951 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨14, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (20898224675867 / 25000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302594884951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_15 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (83558144493933 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302598874571 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨15, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (83558144493933 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302598874571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_16 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (83523414900043 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302602871629 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨16, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (83523414900043 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302602871629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_17 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (83488709887517 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302606882079 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨17, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (83488709887517 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302606882079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_18 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (333816117689 / 400000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302610853443 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨18, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (333816117689 / 400000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302610853443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_19 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (83419373470313 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151307424667 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨19, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (83419373470313 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151307424667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12312_0 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (42041022905801 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (115119833403 / 5000000000000 : ℝ))
      (E := (cell12312 ⟨0, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (42041022905801 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (115119833403 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_1 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (21011735904151 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302400683351 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨1, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (21011735904151 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302400683351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_2 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (84011866536099 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302404654421 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨2, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (84011866536099 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302404654421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_3 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (16795362906637 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460481729737 / 20000000000000 : ℝ))
      (E := (cell12312 ⟨3, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (16795362906637 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460481729737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_4 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83941787571157 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (287801584441 / 12500000000000 : ℝ))
      (E := (cell12312 ⟨4, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83941787571157 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (287801584441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_5 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (1311043525211 / 1562500000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302416628303 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨5, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (1311043525211 / 1562500000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302416628303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_6 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83871808623907 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302420631553 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨6, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83871808623907 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302420631553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_7 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83836856566237 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302424635957 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨7, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83836856566237 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302424635957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_8 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20950482351139 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460485729959 / 20000000000000 : ℝ))
      (E := (cell12312 ⟨8, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20950482351139 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460485729959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_9 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83767027103117 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151216311557 / 50000000000000 : ℝ))
      (E := (cell12312 ⟨9, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83767027103117 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151216311557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_10 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83732149626357 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302436621619 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨10, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83732149626357 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302436621619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_11 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41848648469451 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460488118961 / 20000000000000 : ℝ))
      (E := (cell12312 ⟨11, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41848648469451 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460488118961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_12 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83662469005561 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302444607919 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨12, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83662469005561 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302444607919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_13 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (8362766579133 / 10000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302448609903 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨13, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (8362766579133 / 10000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302448609903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_14 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (16718577452277 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302452607457 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨14, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (16718577452277 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302452607457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_15 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20889533345271 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (230245660703 / 10000000000000 : ℝ))
      (E := (cell12312 ⟨15, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20889533345271 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (230245660703 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_16 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83523404115967 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302460556679 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨16, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83523404115967 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302460556679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_17 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (10436087428969 / 12500000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (18419716629 / 800000000000 : ℝ))
      (E := (cell12312 ⟨17, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (10436087428969 / 12500000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (18419716629 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_18 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41727009647167 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302468562269 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨18, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41727009647167 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302468562269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_19 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (83419363669789 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (115123628561 / 5000000000000 : ℝ))
      (E := (cell12312 ⟨19, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (83419363669789 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (115123628561 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12313_0 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (42041014856869 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302254444413 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨0, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (42041014856869 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302254444413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_1 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (84046927854511 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (460451691733 / 20000000000000 : ℝ))
      (E := (cell12313 ⟨1, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (84046927854511 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (460451691733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_2 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (84011851109301 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575565607373 / 25000000000000 : ℝ))
      (E := (cell12313 ⟨2, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (84011851109301 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575565607373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_3 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83976799441207 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302266424311 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨3, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83976799441207 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302266424311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_4 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (3357670912541 / 4000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151135197321 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨4, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (3357670912541 / 4000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151135197321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_5 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83906771189743 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151137203713 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨5, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83906771189743 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151137203713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_6 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (16774358906709 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302278413617 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨6, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (16774358906709 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302278413617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_7 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83836842808803 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (115114118191 / 5000000000000 : ℝ))
      (E := (cell12313 ⟨7, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83836842808803 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (115114118191 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_8 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83801915979581 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302286382159 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨8, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83801915979581 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302286382159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_9 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83767014010129 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302290360771 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨9, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83767014010129 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302290360771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_10 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (8373213686489 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151147182679 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨10, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (8373213686489 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151147182679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_11 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (83697284508487 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287787293177 / 12500000000000 : ℝ))
      (E := (cell12313 ⟨11, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (83697284508487 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287787293177 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_12 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41831228452867 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575575591547 / 25000000000000 : ℝ))
      (E := (cell12313 ⟨12, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41831228452867 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575575591547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_13 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (10453456752703 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302306376619 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨13, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (10453456752703 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302306376619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_14 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (16718575164267 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302310325309 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨14, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (16718575164267 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302310325309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_15 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (20889530567557 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575578583719 / 25000000000000 : ℝ))
      (E := (cell12313 ⟨15, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (20889530567557 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575578583719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_16 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41761696666921 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287789794181 / 12500000000000 : ℝ))
      (E := (cell12313 ⟨16, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41761696666921 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287789794181 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_17 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (10436086122237 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302322328813 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨17, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (10436086122237 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302322328813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_18 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (2607937786509 / 3125000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302326324801 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨18, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (2607937786509 / 3125000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302326324801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_19 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (20854838467773 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302330288663 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨19, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (20854838467773 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302330288663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12314_0 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (84082013618491 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302112273281 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨0, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (84082013618491 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302112273281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_1 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (42023456047497 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302116286559 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨1, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (42023456047497 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302116286559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_2 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (84011835685037 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302120257211 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨2, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (84011835685037 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302120257211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_3 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83976784351721 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302124252651 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨3, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83976784351721 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302124252651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_4 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41970879029171 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (5755320561 / 250000000000 : ℝ))
      (E := (cell12314 ⟨4, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41970879029171 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (5755320561 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_5 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (8390675676839 / 10000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575533059849 / 25000000000000 : ℝ))
      (E := (cell12314 ⟨5, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (8390675676839 / 10000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575533059849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_6 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (1677435608911 / 2000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302136248593 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨6, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (1677435608911 / 2000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302136248593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_7 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41918414526847 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575535050649 / 25000000000000 : ℝ))
      (E := (cell12314 ⟨7, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41918414526847 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575535050649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_8 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83801902556887 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151072112763 / 50000000000000 : ℝ))
      (E := (cell12314 ⟨8, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83801902556887 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151072112763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_9 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83767000919383 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (28776852619 / 1250000000000 : ℝ))
      (E := (cell12314 ⟨9, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83767000919383 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (28776852619 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_10 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41866062052811 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (57553805507 / 2500000000000 : ℝ))
      (E := (cell12314 ⟨10, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41866062052811 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (57553805507 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_11 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83697272080231 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302156207297 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨11, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83697272080231 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302156207297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_12 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41831222404011 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302160177769 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨12, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41831222404011 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302160177769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_13 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (10453455281749 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302164196713 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨13, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (10453455281749 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302164196713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_14 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83592864383319 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302168154701 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨14, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83592864383319 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302168154701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_15 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (20889527790341 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (143885760897 / 6250000000000 : ℝ))
      (E := (cell12314 ⟨15, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (20889527790341 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (143885760897 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_16 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (20880845638417 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (143886009103 / 6250000000000 : ℝ))
      (E := (cell12314 ⟨16, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (20880845638417 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (143886009103 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_17 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83488678525951 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (14388625829 / 625000000000 : ℝ))
      (E := (cell12314 ⟨17, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83488678525951 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (14388625829 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_18 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (83453999044111 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151092070519 / 50000000000000 : ℝ))
      (E := (cell12314 ⟨18, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (83453999044111 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151092070519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_19 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (5213709004639 / 6250000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575547029523 / 25000000000000 : ℝ))
      (E := (cell12314 ⟨19, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (5213709004639 / 6250000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575547029523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12315_0 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (42040998762931 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460394030933 / 20000000000000 : ℝ))
      (E := (cell12315 ⟨0, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (42040998762931 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460394030933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_1 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (84046896338053 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (575493541759 / 25000000000000 : ℝ))
      (E := (cell12315 ⟨1, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (84046896338053 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (575493541759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_2 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (42005910131653 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2301978137581 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨2, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (42005910131653 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2301978137581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_3 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (3359070770589 / 4000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2301982133709 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨3, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (3359070770589 / 4000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2301982133709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_4 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (10492717913201 / 12500000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (575496541201 / 25000000000000 : ℝ))
      (E := (cell12315 ⟨4, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (10492717913201 / 12500000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (575496541201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_5 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20976685587361 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2301990124217 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨5, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20976685587361 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2301990124217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_6 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83871766359919 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2301994136487 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨6, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83871766359919 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2301994136487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_7 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20959203825227 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460399618871 / 20000000000000 : ℝ))
      (E := (cell12315 ⟨7, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20959203825227 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460399618871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_8 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20950472284119 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302002121943 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨8, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20950472284119 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302002121943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_9 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83766987830877 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (287750763923 / 12500000000000 : ℝ))
      (E := (cell12315 ⟨9, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83766987830877 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (287750763923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_10 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83732111348553 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151005064191 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨10, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83732111348553 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151005064191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_11 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20924314913533 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302014122427 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨11, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20924314913533 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302014122427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_12 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83662432712427 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302018100713 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨12, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83662432712427 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302018100713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_13 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16725526097687 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151011035093 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨13, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16725526097687 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151011035093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_14 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (10449106618417 / 12500000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (575506523909 / 25000000000000 : ℝ))
      (E := (cell12315 ⟨14, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (10449106618417 / 12500000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (575506523909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_15 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20889525013623 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (115101503367 / 5000000000000 : ℝ))
      (E := (cell12315 ⟨15, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20889525013623 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (115101503367 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_16 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16704674355089 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302034049569 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨16, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16704674355089 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302034049569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_17 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16697733615183 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302038048279 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨17, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16697733615183 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302038048279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_18 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83453988921803 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (92081682767 / 4000000000000 : ℝ))
      (E := (cell12315 ⟨18, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83453988921803 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (92081682767 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_19 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (83419334279183 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (230204605951 / 10000000000000 : ℝ))
      (E := (cell12315 ⟨19, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (83419334279183 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (230204605951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12316_0 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (1681639628717 / 2000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (71932129573 / 3125000000000 : ℝ))
      (E := (cell12316 ⟨0, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (1681639628717 / 2000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (71932129573 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_1 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (42023440291843 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301832157891 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨1, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (42023440291843 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301832157891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_2 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (21002951211027 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301836128417 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨2, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (21002951211027 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301836128417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_3 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83976754180221 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575460031331 / 25000000000000 : ℝ))
      (E := (cell12316 ⟨3, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83976754180221 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575460031331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_4 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41970864277661 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301844100131 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨4, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41970864277661 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301844100131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_5 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (16781345586581 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150924059887 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨5, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (16781345586581 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150924059887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_6 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41935876138327 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (287731516901 / 12500000000000 : ℝ))
      (E := (cell12316 ⟨6, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41935876138327 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (287731516901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_7 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41918400775223 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301856097031 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨7, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41918400775223 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301856097031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_8 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41900937859173 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (230186007141 / 10000000000000 : ℝ))
      (E := (cell12316 ⟨8, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41900937859173 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (230186007141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_9 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83766974744611 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (460372813273 / 20000000000000 : ℝ))
      (E := (cell12316 ⟨9, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83766974744611 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (460372813273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_10 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41866049296841 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575467022417 / 25000000000000 : ℝ))
      (E := (cell12316 ⟨10, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41866049296841 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575467022417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_11 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83697247230189 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301872090807 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨11, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83697247230189 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301872090807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_12 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41831210309473 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150938038487 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨12, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41831210309473 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150938038487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_13 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (10453452340619 / 12500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150940027557 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨13, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (10453452340619 / 12500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1150940027557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_14 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41796420756693 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301884031921 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨14, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41796420756693 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301884031921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_15 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (20889522237403 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (57547201799 / 2500000000000 : ℝ))
      (E := (cell12316 ⟨15, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (20889522237403 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (57547201799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_16 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (20880840249793 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301892065213 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨16, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (20880840249793 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301892065213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_17 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (83488657627789 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301896017561 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨17, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (83488657627789 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301896017561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_18 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41726989400681 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301900051023 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨18, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41726989400681 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301900051023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_19 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (5213707780373 / 6250000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301903996491 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨19, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (5213707780373 / 6250000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301903996491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12317_0 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (42040982674227 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301686190527 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨0, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (42040982674227 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301686190527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_1 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (21011716207973 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150845100667 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨1, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (21011716207973 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150845100667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_2 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (42005894713721 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301694171907 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨2, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (42005894713721 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301694171907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_3 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41988369549103 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301698169659 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨3, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41988369549103 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301698169659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_4 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (16788342761497 / 20000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150851073053 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨4, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (16788342761497 / 20000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150851073053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_5 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (20976678379693 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150853084093 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨5, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (20976678379693 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150853084093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_6 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83871738195753 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (71928443339 / 3125000000000 : ℝ))
      (E := (cell12317 ⟨6, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83871738195753 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (71928443339 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_7 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41918393901153 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301714152693 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨7, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41918393901153 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301714152693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_8 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83801862302497 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460343626377 / 20000000000000 : ℝ))
      (E := (cell12317 ⟨8, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83801862302497 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460343626377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_9 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (10470870207573 / 12500000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460344426489 / 20000000000000 : ℝ))
      (E := (cell12317 ⟨9, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (10470870207573 / 12500000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460344426489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_10 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83732085841009 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301726104139 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨10, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83732085841009 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301726104139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_11 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83697234808403 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (575432528109 / 25000000000000 : ℝ))
      (E := (cell12317 ⟨11, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83697234808403 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (575432528109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_12 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83662408527581 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301734106551 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨12, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83662408527581 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301734106551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_13 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41813803481771 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (92069523737 / 4000000000000 : ℝ))
      (E := (cell12317 ⟨13, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41813803481771 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (92069523737 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_14 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (20898207520367 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301742079751 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨14, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (20898207520367 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301742079751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_15 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41779038923361 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (92069842879 / 4000000000000 : ℝ))
      (E := (cell12317 ⟨15, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41779038923361 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (92069842879 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_16 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (5220209389053 / 6250000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150875038147 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨16, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (5220209389053 / 6250000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150875038147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_17 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (8348864718157 / 10000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150877049329 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨17, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (8348864718157 / 10000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150877049329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_18 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (20863492170697 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (287719760823 / 12500000000000 : ℝ))
      (E := (cell12317 ⟨18, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (20863492170697 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (287719760823 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_19 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (83419314694581 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150881022731 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨19, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (83419314694581 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150881022731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12318_0 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (84081949263673 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (230154434501 / 10000000000000 : ℝ))
      (E := (cell12318 ⟨0, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (84081949263673 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (230154434501 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_1 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (84046849082673 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575387074341 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨1, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (84046849082673 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575387074341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_2 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (84011774013307 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301552325869 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨2, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (84011774013307 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301552325869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_3 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83976724018681 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575389081139 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨3, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83976724018681 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575389081139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_4 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (16788339812419 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150780151367 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨4, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (16788339812419 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150780151367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_5 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (20976674776761 / 25000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301564269453 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨5, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (20976674776761 / 25000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301564269453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_6 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (2620991378663 / 3125000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (230156829141 / 10000000000000 : ℝ))
      (E := (cell12318 ⟨6, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (2620991378663 / 3125000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (230156829141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_7 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (10479596757061 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301572261343 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨7, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (10479596757061 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301572261343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_8 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (2618807777779 / 3125000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (287697030677 / 12500000000000 : ℝ))
      (E := (cell12318 ⟨8, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (2618807777779 / 3125000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (287697030677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_9 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (16753389715759 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301580251647 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨9, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (16753389715759 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301580251647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_10 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83732073090533 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301584229799 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨10, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83732073090533 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301584229799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_11 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (20924305597193 / 25000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150794122673 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨11, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (20924305597193 / 25000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150794122673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_12 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83662396438329 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150796123749 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨12, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83662396438329 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150796123749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_13 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (20906898801051 / 25000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575399060799 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨13, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (20906898801051 / 25000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575399060799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_14 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83592818651581 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301600239131 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨14, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83592818651581 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301600239131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_15 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41779033372911 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (9206416967 / 400000000000 : ℝ))
      (E := (cell12318 ⟨15, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41779033372911 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (9206416967 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_16 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41761669726237 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301608199101 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨16, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41761669726237 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301608199101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_17 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (4174431836863 / 5000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301612233403 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨17, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (4174431836863 / 5000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301612233403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_18 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41726979283041 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301616175857 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨18, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41726979283041 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301616175857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_19 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (83419304905019 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575405051607 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨19, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (83419304905019 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575405051607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12319_0 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (84081933181507 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460280510403 / 20000000000000 : ℝ))
      (E := (cell12319 ⟨0, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (84081933181507 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460280510403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_1 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (42023416668013 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (71918953243 / 3125000000000 : ℝ))
      (E := (cell12319 ⟨1, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (42023416668013 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (71918953243 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_2 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (84011758601703 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150705266243 / 50000000000000 : ℝ))
      (E := (cell12319 ⟨2, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (84011758601703 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150705266243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_3 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (20994177235411 / 25000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460282894867 / 20000000000000 : ℝ))
      (E := (cell12319 ⟨3, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (20994177235411 / 25000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460282894867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_4 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (5246355269947 / 6250000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301418512151 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨4, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (5246355269947 / 6250000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301418512151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_5 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41953342348861 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (115071124073 / 5000000000000 : ℝ))
      (E := (cell12319 ⟨5, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41953342348861 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (115071124073 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_6 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41935855020521 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575356626701 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨6, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41935855020521 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575356626701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_7 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (83836760312991 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575357620229 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨7, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (83836760312991 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575357620229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_8 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (83801835477639 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301434469957 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨8, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (83801835477639 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301434469957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_9 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (16753387099849 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575359620487 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨9, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (16753387099849 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575359620487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_10 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (83732060342253 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575360616663 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨10, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (83732060342253 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575360616663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_11 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (2615537811603 / 3125000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301446431509 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨11, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (2615537811603 / 3125000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301446431509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_12 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (83662384351191 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575362610441 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨12, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (83662384351191 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575362610441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_13 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (4181379172347 / 5000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (46029088927 / 2000000000000 : ℝ))
      (E := (cell12319 ⟨13, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (4181379172347 / 5000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (46029088927 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_14 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (3343712288949 / 4000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150729225981 / 50000000000000 : ℝ))
      (E := (cell12319 ⟨14, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (3343712288949 / 4000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150729225981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_15 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (83558055646913 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150731203459 / 50000000000000 : ℝ))
      (E := (cell12319 ⟨15, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (83558055646913 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150731203459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_16 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (1305052010657 / 1562500000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575366608409 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨16, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (1305052010657 / 1562500000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575366608409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_17 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (83488626294857 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301470421797 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨17, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (83488626294857 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301470421797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_18 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41726974225621 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575368594259 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨18, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41726974225621 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575368594259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_19 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41709647558641 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150739210587 / 50000000000000 : ℝ))
      (E := (cell12319 ⟨19, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41709647558641 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150739210587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12320_0 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (21020479275489 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (287657601443 / 12500000000000 : ℝ))
      (E := (cell12320 ⟨0, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (21020479275489 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (287657601443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_1 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (84046817591951 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (115063238139 / 5000000000000 : ℝ))
      (E := (cell12320 ⟨1, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (84046817591951 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (115063238139 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_2 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (21002935798157 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150634395881 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨2, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (21002935798157 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150634395881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_3 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (16795338773419 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301272792519 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨3, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (16795338773419 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301272792519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_4 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (16788333915731 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150638387179 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨4, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (16788333915731 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150638387179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_5 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83906670290803 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301280746327 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨5, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83906670290803 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301280746327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_6 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (8387169596723 / 10000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150642387561 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨6, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (8387169596723 / 10000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150642387561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_7 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (16767349314363 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150644376739 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨7, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (16767349314363 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150644376739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_8 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83801822068629 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (460258549511 / 20000000000000 : ℝ))
      (E := (cell12320 ⟨8, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83801822068629 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (460258549511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_9 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (20941730605483 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (35957761053 / 1562500000000 : ℝ))
      (E := (cell12320 ⟨9, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (20941730605483 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (35957761053 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_10 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83732047596169 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (35957823417 / 1562500000000 : ℝ))
      (E := (cell12320 ⟨10, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83732047596169 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (35957823417 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_11 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (3347887902239 / 4000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150652364477 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨11, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (3347887902239 / 4000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150652364477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_12 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83662372266167 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301308689349 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨12, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83662372266167 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301308689349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_13 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83627571691747 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575328175723 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨13, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83627571691747 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575328175723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_14 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (835927957979 / 1000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575329179561 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨14, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (835927957979 / 1000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575329179561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_15 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (10444755568749 / 12500000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301320683727 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨15, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (10444755568749 / 12500000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301320683727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_16 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83523317913571 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301324663609 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨16, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83523317913571 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301324663609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_17 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83488615854361 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (14383304149 / 625000000000 : ℝ))
      (E := (cell12320 ⟨17, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83488615854361 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (14383304149 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_18 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83453938338267 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301332690123 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨18, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83453938338267 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301332690123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_19 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (83419285331371 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301336689701 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨19, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (83419285331371 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301336689701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12321_0 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (42040950512509 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (5752797809 / 250000000000 : ℝ))
      (E := (cell12321 ⟨0, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (42040950512509 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (5752797809 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_1 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (5252925115653 / 6250000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230112313217 / 10000000000000 : ℝ))
      (E := (cell12321 ⟨1, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (5252925115653 / 6250000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230112313217 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_2 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (21002931946521 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301127103697 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨2, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (21002931946521 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301127103697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_3 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41988339397517 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230113110559 / 10000000000000 : ℝ))
      (E := (cell12321 ⟨3, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41988339397517 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230113110559 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_4 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83941654840603 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (28764188617 / 1250000000000 : ℝ))
      (E := (cell12321 ⟨4, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83941654840603 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (28764188617 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_5 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83906655886289 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301139121939 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨5, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83906655886289 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301139121939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_6 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (4193584094789 / 5000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150571548183 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨6, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (4193584094789 / 5000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150571548183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_7 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (261989790103 / 312500000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (287643384879 / 12500000000000 : ℝ))
      (E := (cell12321 ⟨7, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (261989790103 / 312500000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (287643384879 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_8 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41900904330949 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575287769553 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨8, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41900904330949 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575287769553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_9 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (10470863668357 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301155101923 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨9, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (10470863668357 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301155101923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_10 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83732034852281 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (3595561003 / 156250000000 : ℝ))
      (E := (cell12321 ⟨10, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83732034852281 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (3595561003 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_11 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (10462148142851 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301163079657 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨11, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (10462148142851 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301163079657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_12 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (16732472036651 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230116704831 / 10000000000000 : ℝ))
      (E := (cell12321 ⟨12, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (16732472036651 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230116704831 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_13 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (669020479509 / 800000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150585535449 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨13, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (669020479509 / 800000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150585535449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_14 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (10449098046763 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301175037983 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨14, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (10449098046763 / 12500000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301175037983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_15 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (4177901672753 / 5000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150589507029 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨15, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (4177901672753 / 5000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150589507029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_16 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (522020669669 / 625000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575295751329 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨16, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (522020669669 / 625000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575295751329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_17 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20872151353943 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (287648377213 / 12500000000000 : ℝ))
      (E := (cell12321 ⟨17, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20872151353943 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (287648377213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_18 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (83453928227159 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (460238199747 / 20000000000000 : ℝ))
      (E := (cell12321 ⟨18, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (83453928227159 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (460238199747 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_19 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20854818886821 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575298753003 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨19, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20854818886821 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575298753003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12322_0 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (84081884950693 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150488772977 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨0, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (84081884950693 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150488772977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_1 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (16809357222303 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460196310831 / 20000000000000 : ℝ))
      (E := (cell12322 ⟨1, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (16809357222303 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460196310831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_2 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (21002928095517 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230098552611 / 10000000000000 : ℝ))
      (E := (cell12322 ⟨2, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (21002928095517 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230098552611 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_3 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (4198833186273 / 5000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575247382307 / 25000000000000 : ℝ))
      (E := (cell12322 ⟨3, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (4198833186273 / 5000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575247382307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_4 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (83941640104997 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150496757509 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨4, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (83941640104997 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150496757509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_5 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (83906641484177 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (92039899701 / 4000000000000 : ℝ))
      (E := (cell12322 ⟨5, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (83906641484177 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (92039899701 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_6 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (20967916956673 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301001528447 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨6, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (20967916956673 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301001528447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_7 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (10479589887053 / 12500000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150502757757 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨7, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (10479589887053 / 12500000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150502757757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_8 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (16760359051489 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150504759943 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨8, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (16760359051489 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150504759943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_9 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (83766896274017 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150506745799 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨9, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (83766896274017 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150506745799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_10 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (20933005527647 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575254374087 / 25000000000000 : ℝ))
      (E := (cell12322 ⟨10, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (20933005527647 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575254374087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_11 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41848586365897 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301021483617 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨11, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41848586365897 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301021483617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_12 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (16732469620491 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460205092119 / 20000000000000 : ℝ))
      (E := (cell12322 ⟨12, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (16732469620491 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460205092119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_13 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41813774093787 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301029434219 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨13, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41813774093787 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301029434219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_14 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41796386476169 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (92041338771 / 4000000000000 : ℝ))
      (E := (cell12322 ⟨14, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41796386476169 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (92041338771 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_15 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (83558022362117 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230103745603 / 10000000000000 : ℝ))
      (E := (cell12322 ⟨15, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (83558022362117 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (230103745603 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_16 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (83523296382457 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150520729377 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨16, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (83523296382457 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150520729377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_17 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (5218037186193 / 6250000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150522712611 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨17, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (5218037186193 / 6250000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150522712611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_18 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (16690783623583 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301049419259 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨18, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (16690783623583 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301049419259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_19 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (83419265765021 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301053446323 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨19, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (83419265765021 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301053446323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12323_0 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (4204093443949 / 5000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150418010419 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨0, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (4204093443949 / 5000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150418010419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_1 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (84046770375153 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300840028737 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨1, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (84046770375153 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300840028737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_2 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (4200584849029 / 5000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300844001187 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨2, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (4200584849029 / 5000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300844001187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_3 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20994162164593 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575212001399 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨3, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20994162164593 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575212001399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_4 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (16788325074367 / 20000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300851993473 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨4, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (16788325074367 / 20000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300851993473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_5 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20976656771117 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300856031749 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨5, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20976656771117 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300856031749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_6 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20967913439991 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300860013459 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨6, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20967913439991 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300860013459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_7 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83836705362207 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (17975500039 / 781250000000 : ℝ))
      (E := (cell12323 ⟨7, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83836705362207 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (17975500039 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_8 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83801781855269 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (460173591333 / 20000000000000 : ℝ))
      (E := (cell12323 ⟨8, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83801781855269 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (460173591333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_9 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83766883203413 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300871992383 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨9, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83766883203413 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300871992383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_10 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83732009371089 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150437972983 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨10, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83732009371089 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150437972983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_11 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83697160322933 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150439970419 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨11, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83697160322933 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150439970419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_12 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41831168011883 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150441992129 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨12, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41831168011883 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150441992129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_13 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83627536438593 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150443983541 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨13, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83627536438593 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150443983541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_14 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83592761532601 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150445977013 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨14, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83592761532601 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150445977013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_15 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83558011271161 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (287611993941 / 12500000000000 : ℝ))
      (E := (cell12323 ⟨15, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83558011271161 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (287611993941 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_16 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83523285619821 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575224976909 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨16, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83523285619821 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575224976909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_17 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (8348858454431 / 10000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575225986141 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨17, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (8348858454431 / 10000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575225986141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_18 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (10431738501317 / 12500000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300907893503 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨18, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (10431738501317 / 12500000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2300907893503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_19 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (83419255984581 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (115045596721 / 5000000000000 : ℝ))
      (E := (cell12323 ⟨19, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (83419255984581 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (115045596721 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12324_0 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (84081852809879 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (287586825753 / 12500000000000 : ℝ))
      (E := (cell12324 ⟨0, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (84081852809879 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (287586825753 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_1 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (1050584433017 / 1250000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300698613711 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨1, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (1050584433017 / 1250000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300698613711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_2 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (4200584079081 / 5000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150351293373 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨2, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (4200584079081 / 5000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150351293373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_3 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (8397663359377 / 10000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (287588324067 / 12500000000000 : ℝ))
      (E := (cell12324 ⟨3, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (8397663359377 / 10000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (287588324067 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_4 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (20985402660279 / 25000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (230071058259 / 10000000000000 : ℝ))
      (E := (cell12324 ⟨4, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (20985402660279 / 25000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (230071058259 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_5 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83906612687161 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (46014291319 / 2000000000000 : ℝ))
      (E := (cell12324 ⟨5, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83906612687161 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (46014291319 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_6 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83871639695597 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (11503592757 / 500000000000 : ℝ))
      (E := (cell12324 ⟨6, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83871639695597 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (11503592757 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_7 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (20959172907577 / 25000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575180636867 / 25000000000000 : ℝ))
      (E := (cell12324 ⟨7, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (20959172907577 / 25000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575180636867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_8 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (8380176845537 / 10000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150363281211 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨8, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (8380176845537 / 10000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150363281211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_9 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (16753374027009 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300730546297 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨9, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (16753374027009 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300730546297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_10 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (10466499579223 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (71897953337 / 3125000000000 : ℝ))
      (E := (cell12324 ⟨10, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (10466499579223 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (71897953337 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_11 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (3347885916649 / 4000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575184627337 / 25000000000000 : ℝ))
      (E := (cell12324 ⟨11, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (3347885916649 / 4000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575184627337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_12 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83662323947189 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575185625799 / 25000000000000 : ℝ))
      (E := (cell12324 ⟨12, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83662323947189 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575185625799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_13 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41813762345841 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300746495263 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨13, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41813762345841 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300746495263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_14 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83592750114893 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460150098447 / 20000000000000 : ℝ))
      (E := (cell12324 ⟨14, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83592750114893 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460150098447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_15 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (5222375011387 / 6250000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300754500551 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨15, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (5222375011387 / 6250000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300754500551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_16 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83523274859131 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460151693651 / 20000000000000 : ℝ))
      (E := (cell12324 ⟨16, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83523274859131 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460151693651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_17 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41744287055719 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (8987353357 / 390625000000 : ℝ))
      (E := (cell12324 ⟨17, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41744287055719 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (8987353357 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_18 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (83453897905021 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150383239831 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨18, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (83453897905021 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150383239831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_19 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (16683849241193 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460154095261 / 20000000000000 : ℝ))
      (E := (cell12324 ⟨19, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (16683849241193 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460154095261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

end BstLean.Part263
