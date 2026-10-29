import BstLean.Part268CellShard9Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12575_0 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (84077900398243 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (113354938987 / 5000000000000 : ℝ))
      (E := (cell12575 ⟨0, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (84077900398243 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (113354938987 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_1 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (84042885084473 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267102774777 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨1, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (84042885084473 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267102774777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_2 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (84007894762031 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267106815937 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨2, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (84007894762031 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267106815937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_3 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83972929394291 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133555398329 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨3, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83972929394291 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133555398329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_4 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83937988944817 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267114783607 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨4, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83937988944817 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267114783607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_5 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83903073377367 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267118785369 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨5, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83903073377367 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267118785369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_6 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (5241761415993 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (90684912411 / 4000000000000 : ℝ))
      (E := (cell12575 ⟨6, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (5241761415993 / 6250000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (90684912411 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_7 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83833316744519 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (453425361687 / 20000000000000 : ℝ))
      (E := (cell12575 ⟨7, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83833316744519 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (453425361687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_8 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (2618702362737 / 3125000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (5667826969 / 250000000000 : ℝ))
      (E := (cell12575 ⟨8, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (2618702362737 / 3125000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (5667826969 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_9 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83763659209597 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267134755263 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨9, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83763659209597 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267134755263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_10 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83728867515257 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267138776699 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨10, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83728867515257 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267138776699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_11 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (16738820097889 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566785700229 / 25000000000000 : ℝ))
      (E := (cell12575 ⟨11, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (16738820097889 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566785700229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_12 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83659358097229 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (553502631 / 24414062500 : ℝ))
      (E := (cell12575 ⟨12, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83659358097229 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (553502631 / 24414062500 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_13 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83624640303857 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566787692051 / 25000000000000 : ℝ))
      (E := (cell12575 ⟨13, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83624640303857 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566787692051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_14 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83589947074759 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566788695511 / 25000000000000 : ℝ))
      (E := (cell12575 ⟨14, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83589947074759 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (566788695511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_15 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (16711055675109 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133579382973 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨15, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (16711055675109 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133579382973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_16 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83520634172001 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133581391883 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨16, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83520634172001 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133581391883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_17 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (16697202886019 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133583391407 / 50000000000000 : ℝ))
      (E := (cell12575 ⟨17, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (16697202886019 / 20000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (1133583391407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_18 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (1303928423687 / 1562500000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267170768287 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨18, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (1303928423687 / 1562500000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267170768287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12575_19 : CellCertificate 12575 (890215971315537 / 10000000000000000 : ℝ) (334067552321199 / 200000000000000000 : ℝ) (10546300601077 / 312500000000000 : ℝ)
    (cell12575 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · norm_num [cell12575]
  · have h := gap_lower (n := 12575) (a := (83416848195937 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267174745137 / 100000000000000 : ℝ))
      (E := (cell12575 ⟨19, by decide⟩).energy) (xi := (10546300601077 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12575 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12575]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12575])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12575) (a := (83416848195937 / 100000000000000 : ℝ)) (b := (6552862521 / 4000000000000 : ℝ)) (q := (2267174745137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12575])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12575]

theorem cert12576_0 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (84077884967529 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133485644079 / 50000000000000 : ℝ))
      (E := (cell12576 ⟨0, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (84077884967529 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133485644079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_1 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (42021434989369 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2266975299757 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨1, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (42021434989369 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2266975299757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_2 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (42003939990407 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133489650209 / 50000000000000 : ℝ))
      (E := (cell12576 ⟨2, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (42003939990407 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (1133489650209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_3 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83972914937133 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2266983299241 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨3, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83972914937133 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2266983299241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_4 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (4196898740563 / 5000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (141686706567 / 6250000000000 : ℝ))
      (E := (cell12576 ⟨4, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (4196898740563 / 5000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (141686706567 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_5 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41951529783477 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (453398265299 / 20000000000000 : ℝ))
      (E := (cell12576 ⟨5, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41951529783477 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (453398265299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_6 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83868169168163 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2266995313901 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨6, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83868169168163 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2266995313901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_7 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41916651789513 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566749818823 / 25000000000000 : ℝ))
      (E := (cell12576 ⟨7, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41916651789513 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (566749818823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_8 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83798462763871 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (5667508191 / 250000000000 : ℝ))
      (E := (cell12576 ⟨8, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83798462763871 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (5667508191 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_9 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83763646687209 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267007266783 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨9, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83763646687209 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267007266783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_10 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41864427656871 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267011311713 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨10, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41864427656871 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267011311713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_11 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (2615440269011 / 3125000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267015302141 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨11, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (2615440269011 / 3125000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267015302141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_12 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (20914836634027 / 25000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (70844353213 / 3125000000000 : ℝ))
      (E := (cell12576 ⟨12, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (20914836634027 / 25000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (70844353213 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_13 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41812314531129 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267023262129 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨13, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41812314531129 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267023262129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_14 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41794968076117 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267027302503 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨14, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41794968076117 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267027302503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_15 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (41777633885823 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267031255559 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨15, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (41777633885823 / 50000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267031255559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_16 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83520623886283 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267035301427 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨16, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83520623886283 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267035301427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_17 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83486004462111 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283379908887 / 12500000000000 : ℝ))
      (E := (cell12576 ⟨17, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83486004462111 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (283379908887 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_18 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (83451409465273 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (141690205383 / 6250000000000 : ℝ))
      (E := (cell12576 ⟨18, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (83451409465273 / 100000000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (141690205383 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12576_19 : CellCertificate 12576 (890187500777327 / 10000000000000000 : ℝ) (835102449013581 / 500000000000000000 : ℝ) (33745411406269 / 1000000000000000 : ℝ)
    (cell12576 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · norm_num [cell12576]
  · have h := gap_lower (n := 12576) (a := (10427104857761 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267047293303 / 100000000000000 : ℝ))
      (E := (cell12576 ⟨19, by decide⟩).energy) (xi := (33745411406269 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12576 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12576]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12576])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12576) (a := (10427104857761 / 12500000000000 : ℝ)) (b := (40952093483 / 25000000000000 : ℝ)) (q := (2267047293303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12576])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12576]

theorem cert12577_0 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (84077869539273 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566710962373 / 25000000000000 : ℝ))
      (E := (cell12577 ⟨0, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (84077869539273 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566710962373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_1 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (84042854875419 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (56671196943 / 2500000000000 : ℝ))
      (E := (cell12577 ⟨1, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (84042854875419 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (56671196943 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_2 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (3360314608079 / 4000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283356479743 / 12500000000000 : ℝ))
      (E := (cell12577 ⟨2, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (3360314608079 / 4000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283356479743 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_3 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83972900482313 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133427927467 / 50000000000000 : ℝ))
      (E := (cell12577 ⟨3, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83972900482313 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133427927467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_4 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83937960680001 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266859879711 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨4, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83937960680001 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266859879711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_5 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83903045758799 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (70839495717 / 3125000000000 : ℝ))
      (E := (cell12577 ⟨5, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83903045758799 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (70839495717 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_6 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83868155682657 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266867870829 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨6, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83868155682657 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266867870829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_7 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83833290415713 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566717963369 / 25000000000000 : ℝ))
      (E := (cell12577 ⟨7, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83833290415713 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566717963369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_8 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (10474806240287 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283359477329 / 12500000000000 : ℝ))
      (E := (cell12577 ⟨8, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (10474806240287 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283359477329 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_9 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83763634166921 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266879831797 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨9, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83763634166921 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266879831797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_10 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83728843114287 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266883842253 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨10, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83728843114287 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266883842253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_11 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (261543989779 / 312500000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566721964247 / 25000000000000 : ℝ))
      (E := (cell12577 ⟨11, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (261543989779 / 312500000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566721964247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_12 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (10457416872121 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283361478083 / 12500000000000 : ℝ))
      (E := (cell12577 ⟨12, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (10457416872121 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283361478083 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_13 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41812308911301 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266895809803 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨13, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41812308911301 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266895809803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_14 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83589925231613 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266899818649 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨14, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83589925231613 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266899818649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_15 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (20888814292403 / 25000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133451928599 / 50000000000000 : ℝ))
      (E := (cell12577 ⟨15, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (20888814292403 / 25000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (1133451928599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_16 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (83520613602389 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283363476857 / 12500000000000 : ℝ))
      (E := (cell12577 ⟨16, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (83520613602389 / 100000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (283363476857 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_17 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (10435749311989 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266911813381 / 100000000000000 : ℝ))
      (E := (cell12577 ⟨17, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (10435749311989 / 12500000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (2266911813381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_18 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (41725699908163 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453383171607 / 20000000000000 : ℝ))
      (E := (cell12577 ⟨18, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (41725699908163 / 50000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (453383171607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12577_19 : CellCertificate 12577 (890159034590383 / 10000000000000000 : ℝ) (334014411116673 / 200000000000000000 : ℝ) (67485322689647 / 2000000000000000 : ℝ)
    (cell12577 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · norm_num [cell12577]
  · have h := gap_lower (n := 12577) (a := (20854207382487 / 25000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566729959339 / 25000000000000 : ℝ))
      (E := (cell12577 ⟨19, by decide⟩).energy) (xi := (67485322689647 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12577 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12577]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12577])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12577) (a := (20854207382487 / 25000000000000 : ℝ)) (b := (163795186981 / 100000000000000 : ℝ)) (q := (566729959339 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12577])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12577]

theorem cert12578_0 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (1313716470523 / 1562500000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (453343292749 / 20000000000000 : ℝ))
      (E := (cell12578 ⟨0, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (1313716470523 / 1562500000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (453343292749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_1 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (42021419887259 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133360225421 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨1, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (42021419887259 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133360225421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_2 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (10500981303189 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266724428517 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨2, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (10500981303189 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266724428517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_3 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (8397288602983 / 10000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266728463737 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨3, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (8397288602983 / 10000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266728463737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_4 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (65576520743 / 78125000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266732449633 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨4, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (65576520743 / 78125000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266732449633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_5 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41951515976451 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283342056579 / 12500000000000 : ℝ))
      (E := (cell12578 ⟨5, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41951515976451 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (283342056579 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_6 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (10483517774921 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133370211561 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨6, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (10483517774921 / 12500000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133370211561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_7 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41916638627289 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133372213533 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨7, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41916638627289 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133372213533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_8 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (83798437082861 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133374207147 / 50000000000000 : ℝ))
      (E := (cell12578 ⟨8, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (83798437082861 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (1133374207147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_9 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (83763621648731 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566688112577 / 25000000000000 : ℝ))
      (E := (cell12578 ⟨9, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (83763621648731 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (566688112577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_10 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (20932207729223 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266756426353 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨10, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (20932207729223 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266756426353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_11 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (20923516213057 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266760465459 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨11, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (20923516213057 / 25000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266760465459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_12 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (8365932341981 / 10000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266764458277 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨12, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (8365932341981 / 10000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266764458277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_13 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (83624606584887 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266768411229 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨13, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (83624606584887 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266768411229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_14 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (41794957156447 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (453354489347 / 20000000000000 : ℝ))
      (E := (cell12578 ⟨14, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (41794957156447 / 50000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (453354489347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_15 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (83555246569441 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (453355290913 / 20000000000000 : ℝ))
      (E := (cell12578 ⟨15, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (83555246569441 / 100000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (453355290913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_16 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (4078154459 / 4882812500 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266780440399 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨16, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (4078154459 / 4882812500 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266780440399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_17 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (166971969063 / 200000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (226678440967 / 10000000000000 : ℝ))
      (E := (cell12578 ⟨17, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (166971969063 / 200000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (226678440967 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_18 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (667611121353 / 800000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (35418569153 / 1562500000000 : ℝ))
      (E := (cell12578 ⟨18, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (667611121353 / 800000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (35418569153 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12578_19 : CellCertificate 12578 (890130572753661 / 10000000000000000 : ℝ) (834969617134781 / 500000000000000000 : ℝ) (168699558694927 / 5000000000000000 : ℝ)
    (cell12578 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · norm_num [cell12578]
  · have h := gap_lower (n := 12578) (a := (16683364039903 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266792435541 / 100000000000000 : ℝ))
      (E := (cell12578 ⟨19, by decide⟩).energy) (xi := (168699558694927 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12578 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12578]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12578])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12578) (a := (16683364039903 / 20000000000000 : ℝ)) (b := (40945500543 / 25000000000000 : ℝ)) (q := (2266792435541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12578])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12578]

theorem cert12579_0 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (5254864918133 / 6250000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266589073121 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨0, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (5254864918133 / 6250000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266589073121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_1 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (1313169135563 / 1562500000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (283324134619 / 12500000000000 : ℝ))
      (E := (cell12579 ⟨1, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (1313169135563 / 1562500000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (283324134619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_2 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (3360313426057 / 4000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (113329853607 / 5000000000000 : ℝ))
      (E := (cell12579 ⟨2, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (3360313426057 / 4000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (113329853607 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_3 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41986435789841 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566650266947 / 25000000000000 : ℝ))
      (E := (cell12579 ⟨3, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41986435789841 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566650266947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_4 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41968966212187 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453321014547 / 20000000000000 : ℝ))
      (E := (cell12579 ⟨4, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41968966212187 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (453321014547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_5 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83903018149261 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566652273891 / 25000000000000 : ℝ))
      (E := (cell12579 ⟨5, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83903018149261 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566652273891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_6 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (10483516089787 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266613086661 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨6, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (10483516089787 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266613086661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_7 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (4191663204781 / 5000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266617054027 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨7, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (4191663204781 / 5000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266617054027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_8 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83798424245563 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (70831908231 / 3125000000000 : ℝ))
      (E := (cell12579 ⟨8, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83798424245563 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (70831908231 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_9 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83763609132641 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566656266077 / 25000000000000 : ℝ))
      (E := (cell12579 ⟨9, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83763609132641 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (566656266077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_10 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83728818721557 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133314532007 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨10, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83728818721557 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133314532007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_11 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83694052977197 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (4533266139 / 200000000000 : ℝ))
      (E := (cell12579 ⟨11, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83694052977197 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (4533266139 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_12 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (10457413983079 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133318543751 / 50000000000000 : ℝ))
      (E := (cell12579 ⟨12, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (10457413983079 / 12500000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (1133318543751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_13 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41812297674557 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266641066407 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨13, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41812297674557 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266641066407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_14 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83589903396077 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266645070513 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨14, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83589903396077 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266645070513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_15 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (41777617985567 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141665565479 / 6250000000000 : ℝ))
      (E := (cell12579 ⟨15, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (41777617985567 / 50000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (141665565479 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_16 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (20880148260019 / 25000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266653061713 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨16, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (20880148260019 / 25000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266653061713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_17 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83485974568873 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266657059967 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨17, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83485974568873 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266657059967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_18 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83451380523671 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266661047619 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨18, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83451380523671 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266661047619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12579_19 : CellCertificate 12579 (178020423053223 / 2000000000000000 : ℝ) (208725804260089 / 125000000000000000 : ℝ) (10542863308947 / 312500000000000 : ℝ)
    (cell12579 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · norm_num [cell12579]
  · have h := gap_lower (n := 12579) (a := (83416810870791 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266665087859 / 100000000000000 : ℝ))
      (E := (cell12579 ⟨19, by decide⟩).energy) (xi := (10542863308947 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12579 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12579]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12579])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12579) (a := (83416810870791 / 100000000000000 : ℝ)) (b := (81884409751 / 50000000000000 : ℝ)) (q := (2266665087859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12579])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12579]

theorem cert12580_0 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (84077823269239 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (35413465519 / 1562500000000 : ℝ))
      (E := (cell12580 ⟨0, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (84077823269239 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (35413465519 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_1 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (42021404789981 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453293151209 / 20000000000000 : ℝ))
      (E := (cell12580 ⟨1, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (42021404789981 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453293151209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_2 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (84007820879713 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133234884407 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨2, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (84007820879713 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133234884407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_3 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83972857131871 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (113323689141 / 5000000000000 : ℝ))
      (E := (cell12580 ⟨3, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83972857131871 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (113323689141 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_4 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (16787583660001 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133238874507 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨4, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (16787583660001 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133238874507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_5 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83903004347877 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266481791737 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨5, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83903004347877 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266481791737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_6 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41934057619721 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266485745567 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨6, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41934057619721 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266485745567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_7 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (2095831273471 / 2500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133244867179 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨7, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (2095831273471 / 2500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133244867179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_8 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83798411410403 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266493765923 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨8, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83798411410403 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266493765923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_9 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83763596618649 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453299546361 / 20000000000000 : ℝ))
      (E := (cell12580 ⟨9, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83763596618649 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453299546361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_10 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (2093220163207 / 2500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133250877619 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨10, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (2093220163207 / 2500000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133250877619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_11 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (16738808220837 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133252863583 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨11, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (16738808220837 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133252863583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_12 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (16731860062287 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453301954083 / 20000000000000 : ℝ))
      (E := (cell12580 ⟨12, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (16731860062287 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (453301954083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_13 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (41812292057641 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266513775339 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨13, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (41812292057641 / 50000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266513775339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_14 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83589892481163 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133258874053 / 50000000000000 : ℝ))
      (E := (cell12580 ⟨14, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83589892481163 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (1133258874053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_15 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83555225374689 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (283315219099 / 12500000000000 : ℝ))
      (E := (cell12580 ⟨15, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83555225374689 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (283315219099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_16 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (16704116552331 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (226652573697 / 10000000000000 : ℝ))
      (E := (cell12580 ⟨16, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (16704116552331 / 20000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (226652573697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_17 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83485964608031 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266529764271 / 100000000000000 : ℝ))
      (E := (cell12580 ⟨17, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83485964608031 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (2266529764271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_18 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83451370879963 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566633430879 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨18, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83451370879963 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566633430879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12580_19 : CellCertificate 12580 (890073662126701 / 10000000000000000 : ℝ) (26088650859559 / 15625000000000000 : ℝ) (337344138936343 / 10000000000000000 : ℝ)
    (cell12580 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · norm_num [cell12580]
  · have h := gap_lower (n := 12580) (a := (83416801543773 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566634434017 / 25000000000000 : ℝ))
      (E := (cell12580 ⟨19, by decide⟩).energy) (xi := (337344138936343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12580 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12580]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12580])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12580) (a := (83416801543773 / 100000000000000 : ℝ)) (b := (163755638973 / 100000000000000 : ℝ)) (q := (566634434017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12580])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12580]

theorem cert12581_0 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (21019451962701 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566583627109 / 25000000000000 : ℝ))
      (E := (cell12581 ⟨0, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (21019451962701 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566583627109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_1 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (42021397243153 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266338488127 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨1, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (42021397243153 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266338488127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_2 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (84007806110377 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266342518537 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨2, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (84007806110377 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266342518537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_3 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41986421343197 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (22663464931 / 1000000000000 : ℝ))
      (E := (cell12581 ⟨3, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41986421343197 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (22663464931 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_4 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83937904177931 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (283293809809 / 12500000000000 : ℝ))
      (E := (cell12581 ⟨4, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83937904177931 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (283293809809 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_5 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83902990548749 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133177241619 / 50000000000000 : ℝ))
      (E := (cell12581 ⟨5, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83902990548749 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (1133177241619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_6 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83868101762803 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266358457781 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨6, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83868101762803 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266358457781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_7 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (20958309446059 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266362468061 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨7, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (20958309446059 / 25000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266362468061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_8 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (4189919928869 / 5000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (453273292781 / 20000000000000 : ℝ))
      (E := (cell12581 ⟨8, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (4189919928869 / 5000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (453273292781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_9 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41881792053377 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266370452803 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨9, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41881792053377 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266370452803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_10 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41864397168531 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (90654980001 / 4000000000000 : ℝ))
      (E := (cell12581 ⟨10, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41864397168531 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (90654980001 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_11 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (10461753654149 / 12500000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566594624129 / 25000000000000 : ℝ))
      (E := (cell12581 ⟨11, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (10461753654149 / 12500000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566594624129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_12 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83659288760217 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266382448941 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨12, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83659288760217 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266382448941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_13 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83624572883391 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266386479923 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨13, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83624572883391 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266386479923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_14 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83589881568149 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266390479519 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨14, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83589881568149 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266390479519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_15 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83555214780107 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566598613413 / 25000000000000 : ℝ))
      (E := (cell12581 ⟨15, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83555214780107 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (566598613413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_16 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41760286242529 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266398466173 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨16, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41760286242529 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266398466173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_17 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (83485954648973 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266402464387 / 100000000000000 : ℝ))
      (E := (cell12581 ⟨17, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (83485954648973 / 100000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (2266402464387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_18 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41725680619 / 50000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (453281290697 / 20000000000000 : ℝ))
      (E := (cell12581 ⟨18, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41725680619 / 50000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (453281290697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12581_19 : CellCertificate 12581 (284814468267 / 3200000000000 : ℝ) (417385224264429 / 250000000000000000 : ℝ) (337316656538729 / 10000000000000000 : ℝ)
    (cell12581 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · norm_num [cell12581]
  · have h := gap_lower (n := 12581) (a := (41708396109231 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (141650656041 / 6250000000000 : ℝ))
      (E := (cell12581 ⟨19, by decide⟩).energy) (xi := (337316656538729 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12581 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12581]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12581])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12581) (a := (41708396109231 / 50000000000000 : ℝ)) (b := (20467807573 / 12500000000000 : ℝ)) (q := (141650656041 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12581])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12581]

theorem cert12582_0 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (10509724054353 / 12500000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (113310363829 / 5000000000000 : ℝ))
      (E := (cell12582 ⟨0, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (10509724054353 / 12500000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (113310363829 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_1 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (16808555879013 / 20000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266211273197 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨1, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (16808555879013 / 20000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266211273197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_2 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (42003895671707 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266215263471 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨2, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (42003895671707 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266215263471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_3 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83972828243253 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (141638703531 / 6250000000000 : ℝ))
      (E := (cell12582 ⟨3, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83972828243253 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (141638703531 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_4 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83937890058151 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133111630557 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨4, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83937890058151 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133111630557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_5 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20975744187969 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133113613993 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨5, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20975744187969 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133113613993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_6 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (4193404414419 / 5000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453246244661 / 20000000000000 : ℝ))
      (E := (cell12582 ⟨6, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (4193404414419 / 5000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453246244661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_7 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (163736766859 / 195312500000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133117627569 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨7, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (163736766859 / 195312500000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133117627569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_8 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (41899192873247 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266239273311 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨8, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (41899192873247 / 50000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266239273311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_9 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83763571596957 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266243227303 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨9, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83763571596957 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266243227303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_10 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83728782147901 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133123620173 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨10, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83728782147901 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133123620173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_11 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83694017364217 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (885254399 / 39062500000 : ℝ))
      (E := (cell12582 ⟨11, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83694017364217 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (885254399 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_12 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83659277210979 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133127619619 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨12, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83659277210979 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133127619619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_13 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (261326755167 / 312500000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266259238263 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨13, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (261326755167 / 312500000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266259238263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_14 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83589870657037 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (141641454047 / 6250000000000 : ℝ))
      (E := (cell12582 ⟨14, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83589870657037 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (141641454047 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_15 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83555204187387 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133133633273 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨15, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83555204187387 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133133633273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_16 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (20880140552571 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266271249323 / 100000000000000 : ℝ))
      (E := (cell12582 ⟨16, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (20880140552571 / 25000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (2266271249323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_17 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83485944691699 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453255043703 / 20000000000000 : ℝ))
      (E := (cell12582 ⟨17, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83485944691699 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (453255043703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_18 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83451351597783 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (283284904691 / 12500000000000 : ℝ))
      (E := (cell12582 ⟨18, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83451351597783 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (283284904691 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12582_19 : CellCertificate 12582 (222504192222023 / 2500000000000000 : ℝ) (834704080106747 / 500000000000000000 : ℝ) (16864458934611 / 500000000000000 : ℝ)
    (cell12582 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · norm_num [cell12582]
  · have h := gap_lower (n := 12582) (a := (83416782894857 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133141626569 / 50000000000000 : ℝ))
      (E := (cell12582 ⟨19, by decide⟩).energy) (xi := (16864458934611 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12582 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12582]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12582])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12582) (a := (83416782894857 / 100000000000000 : ℝ)) (b := (163729284333 / 100000000000000 : ℝ)) (q := (1133141626569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12582])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12582]

theorem cert12583_0 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (84077777021297 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (45321601953 / 2000000000000 : ℝ))
      (E := (cell12583 ⟨0, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (84077777021297 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (45321601953 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_1 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (84042764306237 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566521013359 / 25000000000000 : ℝ))
      (E := (cell12583 ⟨1, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (84042764306237 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566521013359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_2 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (42003888289413 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266088061457 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨2, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (42003888289413 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266088061457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_3 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (16794562760489 / 20000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566523018253 / 25000000000000 : ℝ))
      (E := (cell12583 ⟨3, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (16794562760489 / 20000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566523018253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_4 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83937875940667 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (453219207809 / 20000000000000 : ℝ))
      (E := (cell12583 ⟨4, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83937875940667 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (453219207809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_5 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83902962957257 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (283262510487 / 12500000000000 : ℝ))
      (E := (cell12583 ⟨5, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83902962957257 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (283262510487 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_6 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20967018704043 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (113305202107 / 5000000000000 : ℝ))
      (E := (cell12583 ⟨6, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20967018704043 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (113305202107 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_7 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20958302870389 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566527009407 / 25000000000000 : ℝ))
      (E := (cell12583 ⟨7, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20958302870389 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566527009407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_8 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (5237398307359 / 6250000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266112078169 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨8, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (5237398307359 / 6250000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266112078169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_9 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (10470444886157 / 12500000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (453223211061 / 20000000000000 : ℝ))
      (E := (cell12583 ⟨9, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (10470444886157 / 12500000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (453223211061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_10 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41864384980399 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266120034233 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨10, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41864384980399 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266120034233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_11 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83694005497261 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266124021937 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨11, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83694005497261 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266124021937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_12 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83659265663719 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266128025151 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨12, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83659265663719 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266128025151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_13 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20906137606357 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266132050361 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨13, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20906137606357 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266132050361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_14 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41794929873913 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133068022839 / 50000000000000 : ℝ))
      (E := (cell12583 ⟨14, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41794929873913 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (1133068022839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_15 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (5222199599783 / 6250000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (90645600681 / 4000000000000 : ℝ))
      (E := (cell12583 ⟨15, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (5222199599783 / 6250000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (90645600681 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_16 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (20880137984333 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (283268003531 / 12500000000000 : ℝ))
      (E := (cell12583 ⟨16, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (20880137984333 / 25000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (283268003531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_17 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (83485934736209 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566537006663 / 25000000000000 : ℝ))
      (E := (cell12583 ⟨17, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (83485934736209 / 100000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (566537006663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_18 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (8345134195931 / 10000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (90646080697 / 4000000000000 : ℝ))
      (E := (cell12583 ⟨18, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (8345134195931 / 10000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (90646080697 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12583_19 : CellCertificate 12583 (88998832878681 / 1000000000000000 : ℝ) (834637722237039 / 500000000000000000 : ℝ) (168630852697787 / 5000000000000000 : ℝ)
    (cell12583 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · norm_num [cell12583]
  · have h := gap_lower (n := 12583) (a := (41708386786479 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266156063757 / 100000000000000 : ℝ))
      (E := (cell12583 ⟨19, by decide⟩).energy) (xi := (168630852697787 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12583 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12583]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12583])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12583) (a := (41708386786479 / 50000000000000 : ℝ)) (b := (163716110221 / 100000000000000 : ℝ)) (q := (2266156063757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12583])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12583]

theorem cert12584_0 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (84077761610223 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265952913849 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨0, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (84077761610223 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265952913849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_1 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (42021374609911 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (283244618061 / 12500000000000 : ℝ))
      (E := (cell12584 ⟨1, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (42021374609911 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (283244618061 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_2 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (84007761816611 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265960912499 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨2, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (84007761816611 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265960912499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_3 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (8397279936397 / 10000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265964884779 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨3, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (8397279936397 / 10000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265964884779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_4 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (3357514473019 / 4000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265968928053 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨4, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (3357514473019 / 4000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265968928053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_5 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (20975737291223 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265972935139 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨5, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (20975737291223 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265972935139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_6 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41934030673089 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265976914287 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨6, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41934030673089 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265976914287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_7 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83833198333479 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453196186291 / 20000000000000 : ℝ))
      (E := (cell12584 ⟨7, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83833198333479 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453196186291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_8 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83798360091129 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1132992439241 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨8, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83798360091129 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1132992439241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_9 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83763546583651 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1132994439401 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨9, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83763546583651 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1132994439401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_10 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (10466094721969 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265992881687 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨10, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (10466094721969 / 12500000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265992881687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_11 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41846996816161 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265996894121 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨11, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41846996816161 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2265996894121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_12 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41829627059219 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266000922837 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨12, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41829627059219 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266000922837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_13 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (20906134799839 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266004916217 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨13, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (20906134799839 / 25000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266004916217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_14 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41794924420257 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566502220107 / 25000000000000 : ℝ))
      (E := (cell12584 ⟨14, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41794924420257 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (566502220107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_15 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83555183007531 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133006439769 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨15, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83555183007531 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133006439769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_16 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41760270833101 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453203383859 / 20000000000000 : ℝ))
      (E := (cell12584 ⟨16, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41760270833101 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (453203383859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_17 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (41742962391251 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133010444401 / 50000000000000 : ℝ))
      (E := (cell12584 ⟨17, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (41742962391251 / 50000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (1133010444401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_18 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (83451332322581 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266024909619 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨18, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (83451332322581 / 100000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266024909619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12584_19 : CellCertificate 12584 (222489973257371 / 2500000000000000 : ℝ) (834571374917217 / 500000000000000000 : ℝ) (337234236647553 / 10000000000000000 : ℝ)
    (cell12584 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · norm_num [cell12584]
  · have h := gap_lower (n := 12584) (a := (16683352850553 / 20000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266028870271 / 100000000000000 : ℝ))
      (E := (cell12584 ⟨19, by decide⟩).energy) (xi := (337234236647553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12584 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12584]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12584])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12584) (a := (16683352850553 / 20000000000000 : ℝ)) (b := (163702938247 / 100000000000000 : ℝ)) (q := (2266028870271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12584])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12584]

theorem cert12585_0 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (84077746201601 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265825782977 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨0, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (84077746201601 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265825782977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_1 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (4202136706791 / 5000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226582983071 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨1, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (4202136706791 / 5000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226582983071 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_2 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (656310523881 / 781250000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (11329169083 / 500000000000 : ℝ))
      (E := (cell12585 ⟨2, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (656310523881 / 781250000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (11329169083 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_3 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (83972784927829 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (141614862971 / 6250000000000 : ℝ))
      (E := (cell12585 ⟨3, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (83972784927829 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (141614862971 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_4 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41968923856289 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265841812353 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨4, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41968923856289 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265841812353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_5 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (83902935374781 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566461445429 / 25000000000000 : ℝ))
      (E := (cell12585 ⟨5, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (83902935374781 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (566461445429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_6 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41934023939199 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226584978181 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨6, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41934023939199 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226584978181 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_7 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (10479148148447 / 12500000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265853820699 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨7, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (10479148148447 / 12500000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265853820699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_8 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (1675966945333 / 2000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132928895111 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨8, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (1675966945333 / 2000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132928895111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_9 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41881767040071 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132930906907 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨9, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41881767040071 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132930906907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_10 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41864372796381 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226586578271 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨10, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41864372796381 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226586578271 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_11 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (418469908847 / 500000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265869761883 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨11, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (418469908847 / 500000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265869761883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_12 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41829621287567 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132936879031 / 50000000000000 : ℝ))
      (E := (cell12585 ⟨12, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41829621287567 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (1132936879031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_13 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41812263987611 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265877777731 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨13, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41812263987611 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265877777731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_14 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41794918967551 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265881769001 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨14, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41794918967551 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265881769001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_15 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (83555172420393 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265885795941 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨15, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (83555172420393 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265885795941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_16 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (41760265698447 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265889806119 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨16, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (41760265698447 / 50000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265889806119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_17 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (83485914830577 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (283236725621 / 12500000000000 : ℝ))
      (E := (cell12585 ⟨17, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (83485914830577 / 100000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (283236725621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_18 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (20862830671899 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226589779767 / 10000000000000 : ℝ))
      (E := (cell12585 ⟨18, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (20862830671899 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (226589779767 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12585_19 : CellCertificate 12585 (27810358175471 / 312500000000000 : ℝ) (166901007628953 / 100000000000000000 : ℝ) (67441354489383 / 2000000000000000 : ℝ)
    (cell12585 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · norm_num [cell12585]
  · have h := gap_lower (n := 12585) (a := (20854188733569 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265901789171 / 100000000000000 : ℝ))
      (E := (cell12585 ⟨19, by decide⟩).energy) (xi := (67441354489383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12585 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12585]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12585])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12585) (a := (20854188733569 / 25000000000000 : ℝ)) (b := (16368976841 / 10000000000000 : ℝ)) (q := (2265901789171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12585])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12585]

theorem cert12586_0 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (84077730795431 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132849381417 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨0, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (84077730795431 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132849381417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_1 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (84042719054229 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265702712107 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨1, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (84042719054229 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265702712107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_2 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (84007732299297 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132853357957 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨2, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (84007732299297 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132853357957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_3 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (4198638524701 / 5000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265710725547 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨3, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (4198638524701 / 5000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265710725547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_4 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (20984458400493 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265714749843 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨4, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (20984458400493 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265714749843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_5 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83902921586923 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (113285936973 / 5000000000000 : ℝ))
      (E := (cell12586 ⟨5, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83902921586923 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (113285936973 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_6 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (2620876075401 / 3125000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265722702647 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨6, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (2620876075401 / 3125000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265722702647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_7 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83833172043847 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (28321583817 / 1250000000000 : ℝ))
      (E := (cell12586 ⟨7, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83833172043847 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (28321583817 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_8 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (16759666888861 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (113286534871 / 5000000000000 : ℝ))
      (E := (cell12586 ⟨8, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (16759666888861 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (113286534871 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_9 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (10470440197341 / 12500000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566433686081 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨9, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (10470440197341 / 12500000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566433686081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_10 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83728733411827 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132869368653 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨10, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83728733411827 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132869368653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_11 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (16738793981699 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (453148548267 / 20000000000000 : ℝ))
      (E := (cell12586 ⟨11, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (16738793981699 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (453148548267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_12 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (5228701939613 / 6250000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (283218338133 / 12500000000000 : ℝ))
      (E := (cell12586 ⟨12, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (5228701939613 / 6250000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (283218338133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_13 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41812258376513 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (141609418313 / 6250000000000 : ℝ))
      (E := (cell12586 ⟨13, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41812258376513 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (141609418313 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_14 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (83589827031589 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (11328773557 / 500000000000 : ℝ))
      (E := (cell12586 ⟨14, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (83589827031589 / 100000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (11328773557 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_15 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (20888790458779 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132879354041 / 50000000000000 : ℝ))
      (E := (cell12586 ⟨15, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (20888790458779 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (1132879354041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_16 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41760260564703 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566440672181 / 25000000000000 : ℝ))
      (E := (cell12586 ⟨16, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41760260564703 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (566440672181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_17 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (16697180976087 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265766716951 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨17, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (16697180976087 / 20000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265766716951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_18 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (41725656527177 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (11328853699 / 500000000000 : ℝ))
      (E := (cell12586 ⟨18, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (41725656527177 / 50000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (11328853699 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12586_19 : CellCertificate 12586 (222475758635633 / 2500000000000000 : ℝ) (1668877423834337 / 1000000000000000000 : ℝ) (168589656396211 / 5000000000000000 : ℝ)
    (cell12586 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · norm_num [cell12586]
  · have h := gap_lower (n := 12586) (a := (20854186404373 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265774703969 / 100000000000000 : ℝ))
      (E := (cell12586 ⟨19, by decide⟩).energy) (xi := (168589656396211 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12586 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12586]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12586])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12586) (a := (20854186404373 / 25000000000000 : ℝ)) (b := (163676600709 / 100000000000000 : ℝ)) (q := (2265774703969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12586])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12586]

theorem cert12587_0 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (84077715391713 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132785868911 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨0, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (84077715391713 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132785868911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_1 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (1680854079501 / 2000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1769981019 / 78125000000 : ℝ))
      (E := (cell12587 ⟨1, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (1680854079501 / 2000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1769981019 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_2 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (42003858772099 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566394931533 / 25000000000000 : ℝ))
      (E := (cell12587 ⟨2, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (42003858772099 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566394931533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_3 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41986378031271 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265583696683 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨3, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41986378031271 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265583696683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_4 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83937819493659 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265587682627 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨4, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83937819493659 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265587682627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_5 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41951453900659 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (113279584627 / 5000000000000 : ℝ))
      (E := (cell12587 ⟨5, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41951453900659 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (113279584627 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_6 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83868020949479 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (707998649 / 31250000000 : ℝ))
      (E := (cell12587 ⟨6, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83868020949479 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (707998649 / 31250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_7 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (20958289725573 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132799850681 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨7, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (20958289725573 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132799850681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_8 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41899160812047 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265603716047 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨8, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41899160812047 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265603716047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_9 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83763509079409 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265607670331 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨9, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83763509079409 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265607670331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_10 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (20932180308237 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265611687439 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨10, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (20932180308237 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265611687439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_11 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41846979024803 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132807858183 / 50000000000000 : ℝ))
      (E := (cell12587 ⟨11, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41846979024803 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (1132807858183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_12 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83659219494459 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (453123941153 / 20000000000000 : ℝ))
      (E := (cell12587 ⟨12, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83659219494459 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (453123941153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_13 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (2613265797899 / 3125000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265623720149 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨13, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (2613265797899 / 3125000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265623720149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_14 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (3343592645199 / 4000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (283203463453 / 12500000000000 : ℝ))
      (E := (cell12587 ⟨14, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (3343592645199 / 4000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (283203463453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_15 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (83555151251699 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265631674111 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨15, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (83555151251699 / 100000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265631674111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_16 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (4176025543187 / 5000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566408920863 / 25000000000000 : ℝ))
      (E := (cell12587 ⟨16, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (4176025543187 / 5000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566408920863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_17 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (41742947466037 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265639682951 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨17, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (41742947466037 / 50000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265639682951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_18 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (10431412927857 / 12500000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566410919447 / 25000000000000 : ℝ))
      (E := (cell12587 ⟨18, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (10431412927857 / 12500000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (566410919447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12587_19 : CellCertificate 12587 (444937305905411 / 5000000000000000 : ℝ) (1668744792463827 / 1000000000000000000 : ℝ) (67430371536567 / 2000000000000000 : ℝ)
    (cell12587 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · norm_num [cell12587]
  · have h := gap_lower (n := 12587) (a := (20854184075603 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265647672909 / 100000000000000 : ℝ))
      (E := (cell12587 ⟨19, by decide⟩).energy) (xi := (67430371536567 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12587 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12587]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12587])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12587) (a := (20854184075603 / 25000000000000 : ℝ)) (b := (32732687029 / 20000000000000 : ℝ)) (q := (2265647672909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12587])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12587]

theorem cert12588_0 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (21019424997611 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (453088941589 / 20000000000000 : ℝ))
      (E := (cell12588 ⟨0, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (21019424997611 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (453088941589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_1 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (84042688898281 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226544874953 / 10000000000000 : ℝ))
      (E := (cell12588 ⟨1, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (84042688898281 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (226544874953 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_2 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (8400770279147 / 10000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132726365783 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨2, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (8400770279147 / 10000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132726365783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_3 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (20993185408349 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265456720943 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨3, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (20993185408349 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265456720943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_4 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83937805387637 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265460726493 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨4, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83937805387637 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265460726493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_5 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (20975723504491 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132732349437 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨5, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (20975723504491 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132732349437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_6 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41934003744169 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265468704271 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨6, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41934003744169 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265468704271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_7 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83833145762909 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (141592043299 / 6250000000000 : ℝ))
      (E := (cell12588 ⟨7, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83833145762909 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (141592043299 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_8 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (654674287547 / 781250000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (453095346027 / 20000000000000 : ℝ))
      (E := (cell12588 ⟨8, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (654674287547 / 781250000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (453095346027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_9 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (10470437072773 / 12500000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265480707857 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨9, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (10470437072773 / 12500000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265480707857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_10 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (20932177264031 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (453096938229 / 20000000000000 : ℝ))
      (E := (cell12588 ⟨10, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (20932177264031 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (453096938229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_11 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (20923486548183 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132744343489 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨11, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (20923486548183 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132744343489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_12 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41829603978543 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132746351043 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨12, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41829603978543 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132746351043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_13 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (5226530894653 / 6250000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132748342423 / 50000000000000 : ℝ))
      (E := (cell12588 ⟨13, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (5226530894653 / 6250000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (1132748342423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_14 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (41794902615129 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (45310013991 / 2000000000000 : ℝ))
      (E := (cell12588 ⟨14, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (41794902615129 / 50000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (45310013991 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_15 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (4177757033507 / 5000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (141594043377 / 6250000000000 : ℝ))
      (E := (cell12588 ⟨15, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (4177757033507 / 5000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (141594043377 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_16 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83520500599893 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265508732137 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨16, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83520500599893 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265508732137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_17 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (16697176997099 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265512702967 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨17, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (16697176997099 / 20000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265512702967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_18 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (83451293793099 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265516728079 / 100000000000000 : ℝ))
      (E := (cell12588 ⟨18, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (83451293793099 / 100000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (2265516728079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12588_19 : CellCertificate 12588 (444923096709449 / 5000000000000000 : ℝ) (417153045543243 / 250000000000000000 : ℝ) (84281101779229 / 2500000000000000 : ℝ)
    (cell12588 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · norm_num [cell12588]
  · have h := gap_lower (n := 12588) (a := (20854181747259 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (283190086999 / 12500000000000 : ℝ))
      (E := (cell12588 ⟨19, by decide⟩).energy) (xi := (84281101779229 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12588 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12588]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12588])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12588) (a := (20854181747259 / 25000000000000 : ℝ)) (b := (163650271717 / 100000000000000 : ℝ)) (q := (283190086999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12588])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12588]

theorem cert12589_0 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (42038842295813 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (707911809 / 31250000000 : ℝ))
      (E := (cell12589 ⟨0, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (42038842295813 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (707911809 / 31250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_1 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (84042673823923 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566330447479 / 25000000000000 : ℝ))
      (E := (cell12589 ⟨1, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (84042673823923 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566330447479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_2 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (10500961005139 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265325790063 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨2, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (10500961005139 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265325790063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_3 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (4198636360329 / 5000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265329798331 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨3, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (4198636360329 / 5000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265329798331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_4 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83937791283907 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265333765657 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨4, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83937791283907 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265333765657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_5 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41951440118431 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132668879231 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨5, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41951440118431 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132668879231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_6 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83867994029409 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265341785061 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨6, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83867994029409 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265341785061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_7 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83833132625699 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265345795551 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨7, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83833132625699 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265345795551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_8 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (10474786998759 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265349797667 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨8, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (10474786998759 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265349797667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_9 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (20940871021763 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132676899447 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨9, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (20940871021763 / 25000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132676899447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_10 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41864348440677 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (90614309937 / 4000000000000 : ℝ))
      (E := (cell12589 ⟨10, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41864348440677 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (90614309937 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_11 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83693934337873 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566340442321 / 25000000000000 : ℝ))
      (E := (cell12589 ⟨11, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83693934337873 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566340442321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_12 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83659196421689 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265365752109 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨12, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83659196421689 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265365752109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_13 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (5226530193629 / 6250000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265369761413 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨13, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (5226530193629 / 6250000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265369761413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_14 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (2089744858311 / 2500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (283171718163 / 12500000000000 : ℝ))
      (E := (cell12589 ⟨14, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (2089744858311 / 2500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (283171718163 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_15 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83555130090441 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566344441961 / 25000000000000 : ℝ))
      (E := (cell12589 ⟨15, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83555130090441 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566344441961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_16 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (41760245168933 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265381776603 / 100000000000000 : ℝ))
      (E := (cell12589 ⟨16, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (41760245168933 / 50000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (2265381776603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_17 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (10435734380087 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566346444251 / 25000000000000 : ℝ))
      (E := (cell12589 ⟨17, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (10435734380087 / 12500000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (566346444251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_18 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (16690256833017 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (226538977423 / 10000000000000 : ℝ))
      (E := (cell12589 ⟨18, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (16690256833017 / 20000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (226538977423 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12589_19 : CellCertificate 12589 (889817779365721 / 10000000000000000 : ℝ) (417119898239187 / 250000000000000000 : ℝ) (84274240273357 / 2500000000000000 : ℝ)
    (cell12589 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · norm_num [cell12589]
  · have h := gap_lower (n := 12589) (a := (83416717677363 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132696886611 / 50000000000000 : ℝ))
      (E := (cell12589 ⟨19, by decide⟩).energy) (xi := (84274240273357 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12589 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12589]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12589])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12589) (a := (83416717677363 / 100000000000000 : ℝ)) (b := (20454638803 / 12500000000000 : ℝ)) (q := (1132696886611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12589])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12589]

theorem cert12590_0 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (84077669195257 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265190864793 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨0, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (84077669195257 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265190864793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_1 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (42021329375987 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265194883303 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨1, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (42021329375987 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265194883303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_2 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (21001918323281 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (18121591213 / 800000000000 : ℝ))
      (E := (cell12590 ⟨2, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (21001918323281 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (18121591213 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_3 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (16794542556419 / 20000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132601435489 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨3, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (16794542556419 / 20000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132601435489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_4 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41968888591233 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453041371603 / 20000000000000 : ℝ))
      (E := (cell12590 ⟨4, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41968888591233 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453041371603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_5 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83902866458011 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566302717827 / 25000000000000 : ℝ))
      (E := (cell12590 ⟨5, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83902866458011 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566302717827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_6 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20966995143173 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (141575928827 / 6250000000000 : ℝ))
      (E := (cell12590 ⟨6, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20966995143173 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (141575928827 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_7 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83833119490661 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (113260944687 / 5000000000000 : ℝ))
      (E := (cell12590 ⟨7, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83833119490661 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (113260944687 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_8 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83798283176259 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (283152857583 / 12500000000000 : ℝ))
      (E := (cell12590 ⟨8, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83798283176259 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (283152857583 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_9 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41881735797007 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132613442717 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨9, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41881735797007 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132613442717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_10 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41864342354319 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132615429641 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨10, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41864342354319 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132615429641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_11 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83693922485029 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265234847173 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨11, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83693922485029 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265234847173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_12 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83659184888267 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566309713959 / 25000000000000 : ℝ))
      (E := (cell12590 ⟨12, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83659184888267 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566309713959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_13 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (2613264746363 / 3125000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566310722937 / 25000000000000 : ℝ))
      (E := (cell12590 ⟨13, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (2613264746363 / 3125000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (566310722937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_14 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83589783436519 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (283155855611 / 12500000000000 : ℝ))
      (E := (cell12590 ⟨14, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83589783436519 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (283155855611 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_15 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83555119512599 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265250837401 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨15, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83555119512599 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265250837401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_16 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (83520480077659 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (90610195001 / 4000000000000 : ℝ))
      (E := (cell12590 ⟨16, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (83520480077659 / 100000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (90610195001 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_17 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (41742932548839 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265258846863 / 100000000000000 : ℝ))
      (E := (cell12590 ⟨17, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (41742932548839 / 50000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (2265258846863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_18 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (20862818634703 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132631437233 / 50000000000000 : ℝ))
      (E := (cell12590 ⟨18, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (20862818634703 / 25000000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (1132631437233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12590_19 : CellCertificate 12590 (111223671206281 / 1250000000000000 : ℝ) (1668347024810131 / 1000000000000000000 : ℝ) (168534759805567 / 5000000000000000 : ℝ)
    (cell12590 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · norm_num [cell12590]
  · have h := gap_lower (n := 12590) (a := (2606772136481 / 3125000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453053369271 / 20000000000000 : ℝ))
      (E := (cell12590 ⟨19, by decide⟩).energy) (xi := (168534759805567 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12590 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12590]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12590])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12590) (a := (2606772136481 / 3125000000000 : ℝ)) (b := (32724790253 / 20000000000000 : ℝ)) (q := (453053369271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12590])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12590]

theorem cert12591_0 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (84077653801337 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132532025761 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨0, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (84077653801337 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132532025761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_1 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (42021321841217 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566267007423 / 25000000000000 : ℝ))
      (E := (cell12591 ⟨1, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (42021321841217 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566267007423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_2 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (42003829273753 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132536004203 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨2, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (42003829273753 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132536004203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_3 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83972698359939 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132537998377 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨3, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83972698359939 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132537998377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_4 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20984440770829 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132540001783 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨4, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20984440770829 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132540001783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_5 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (8390285268141 / 10000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265084037411 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨5, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (8390285268141 / 10000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265084037411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_6 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (16773593423637 / 20000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (90603519629 / 4000000000000 : ℝ))
      (E := (cell12591 ⟨6, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (16773593423637 / 20000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (90603519629 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_7 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41916553178897 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (283136498419 / 12500000000000 : ℝ))
      (E := (cell12591 ⟨7, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41916553178897 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (283136498419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_8 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83798270364579 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (283137004387 / 12500000000000 : ℝ))
      (E := (cell12591 ⟨8, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83798270364579 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (283137004387 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_9 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20940864775767 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265100025487 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨9, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20940864775767 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265100025487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_10 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (3349146901519 / 4000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566276005929 / 25000000000000 : ℝ))
      (E := (cell12591 ⟨10, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (3349146901519 / 4000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566276005929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_11 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83693910634199 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265107978703 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨11, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83693910634199 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265107978703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_12 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (4182958667841 / 5000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265112013267 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨12, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (4182958667841 / 5000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265112013267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_13 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (653316098993 / 781250000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132558008873 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨13, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (653316098993 / 781250000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132558008873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_14 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (41794886271247 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (70784999947 / 3125000000000 : ℝ))
      (E := (cell12591 ⟨14, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (41794886271247 / 50000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (70784999947 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_15 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (16711021787323 / 20000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265124019003 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨15, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (16711021787323 / 20000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265124019003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_16 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (8352046981927 / 10000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265128027407 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨16, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (8352046981927 / 10000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265128027407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_17 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (2087146378911 / 2500000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265132028941 / 100000000000000 : ℝ))
      (E := (cell12591 ⟨17, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (2087146378911 / 2500000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (2265132028941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_18 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (83451264914281 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132568014393 / 50000000000000 : ℝ))
      (E := (cell12591 ⟨18, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (83451264914281 / 100000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (1132568014393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12591_19 : CellCertificate 12591 (11122012053393 / 125000000000000 : ℝ) (16682144777281 / 10000000000000000 : ℝ) (84260520667199 / 2500000000000000 : ℝ)
    (cell12591 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · norm_num [cell12591]
  · have h := gap_lower (n := 12591) (a := (20854174764781 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566284993409 / 25000000000000 : ℝ))
      (E := (cell12591 ⟨19, by decide⟩).energy) (xi := (84260520667199 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12591 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12591]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12591])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12591) (a := (20854174764781 / 25000000000000 : ℝ)) (b := (127820933 / 78125000000 : ℝ)) (q := (566284993409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12591])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12591]

theorem cert12592_0 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (16815527681973 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (226493723339 / 10000000000000 : ℝ))
      (E := (cell12592 ⟨0, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (16815527681973 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (226493723339 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_1 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (84042628615303 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132470614541 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨1, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (84042628615303 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132470614541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_2 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (16801528760851 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (22649452261 / 1000000000000 : ℝ))
      (E := (cell12592 ⟨2, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (16801528760851 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (22649452261 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_3 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (5248292746257 / 6250000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264949175661 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨3, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (5248292746257 / 6250000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264949175661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_4 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (16787549797291 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264953202311 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨4, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (16787549797291 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264953202311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_5 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83902838907059 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264957198857 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨5, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83902838907059 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264957198857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_6 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (2620873552059 / 3125000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264961173541 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨6, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (2620873552059 / 3125000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264961173541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_7 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41916546613549 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132482596157 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨7, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41916546613549 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132482596157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_8 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (8379825755503 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (8847535957 / 390625000000 : ℝ))
      (E := (cell12592 ⟨8, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (8379825755503 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (8847535957 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_9 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41881723307107 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132486609527 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨9, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41881723307107 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132486609527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_10 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (16745732073873 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132488591847 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨10, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (16745732073873 / 20000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132488591847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_11 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41846949392691 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (18119849311 / 800000000000 : ℝ))
      (E := (cell12592 ⟨11, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41846949392691 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (18119849311 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_12 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (20914790456837 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132492583161 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨12, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (20914790456837 / 25000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132492583161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_13 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83624449460527 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132494598757 / 50000000000000 : ℝ))
      (E := (cell12592 ⟨13, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83624449460527 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (1132494598757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_14 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41794880825183 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264993205551 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨14, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41794880825183 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264993205551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_15 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83555098362489 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264997196349 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨15, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83555098362489 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2264997196349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_16 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (835204595627 / 1000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265001175573 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨16, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (835204595627 / 1000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265001175573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_17 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (83485845216981 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453001041369 / 20000000000000 : ℝ))
      (E := (cell12592 ⟨17, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (83485845216981 / 100000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453001041369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_18 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (8345125529149 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265009178971 / 100000000000000 : ℝ))
      (E := (cell12592 ⟨18, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (8345125529149 / 10000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (2265009178971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12592_19 : CellCertificate 12592 (444866281614127 / 5000000000000000 : ℝ) (333616390341127 / 200000000000000000 : ℝ) (337014650265181 / 10000000000000000 : ℝ)
    (cell12592 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · norm_num [cell12592]
  · have h := gap_lower (n := 12592) (a := (41708344876279 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453002631013 / 20000000000000 : ℝ))
      (E := (cell12592 ⟨19, by decide⟩).energy) (xi := (337014650265181 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12592 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12592]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12592])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12592) (a := (41708344876279 / 50000000000000 : ℝ)) (b := (163597639349 / 100000000000000 : ℝ)) (q := (453002631013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12592])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12592]

theorem cert12593_0 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (84077623020841 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132405205199 / 50000000000000 : ℝ))
      (E := (cell12593 ⟨0, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (84077623020841 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132405205199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_1 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (84042613550579 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132407211827 / 50000000000000 : ℝ))
      (E := (cell12593 ⟨1, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (84042613550579 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132407211827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_2 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (84007629063373 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (283102304877 / 12500000000000 : ℝ))
      (E := (cell12593 ⟨2, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (84007629063373 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (283102304877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_3 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83972669522613 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264822407701 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨3, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83972669522613 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264822407701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_4 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83937734891883 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (56620659909 / 2500000000000 : ℝ))
      (E := (cell12593 ⟨4, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83937734891883 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (56620659909 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_5 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20975706283739 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566207603391 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨5, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20975706283739 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566207603391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_6 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83867940215801 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264834409681 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨6, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83867940215801 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264834409681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_7 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20958270024643 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (22648383927 / 1000000000000 : ℝ))
      (E := (cell12593 ⟨7, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20958270024643 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (22648383927 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_8 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20949561186903 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (113242121417 / 5000000000000 : ℝ))
      (E := (cell12593 ⟨8, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20949561186903 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (113242121417 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_9 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20940858531863 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264846408127 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨9, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20940858531863 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264846408127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_10 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83728648202807 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566212599313 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨10, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83728648202807 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566212599313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_11 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41846943469289 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (226485440269 / 10000000000000 : ℝ))
      (E := (cell12593 ⟨11, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41846943469289 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (226485440269 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_12 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83659150299849 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (452971686233 / 20000000000000 : ℝ))
      (E := (cell12593 ⟨12, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83659150299849 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (452971686233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_13 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (16724887650377 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566215607763 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨13, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (16724887650377 / 20000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566215607763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_14 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83589750760133 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264866408507 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨14, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83589750760133 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264866408507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_15 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83555087790219 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264870427593 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨15, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83555087790219 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264870427593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_16 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (20880112326987 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (22648743777 / 1000000000000 : ℝ))
      (E := (cell12593 ⟨16, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (20880112326987 / 25000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (22648743777 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_17 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83485835279301 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132439190287 / 50000000000000 : ℝ))
      (E := (cell12593 ⟨17, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83485835279301 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (1132439190287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_18 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (83451245670439 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264882383243 / 100000000000000 : ℝ))
      (E := (cell12593 ⟨18, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (83451245670439 / 100000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (2264882383243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12593_19 : CellCertificate 12593 (222426041629913 / 2500000000000000 : ℝ) (416987361684429 / 250000000000000000 : ℝ) (84246805599763 / 2500000000000000 : ℝ)
    (cell12593 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · norm_num [cell12593]
  · have h := gap_lower (n := 12593) (a := (41708340223847 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566221597661 / 25000000000000 : ℝ))
      (E := (cell12593 ⟨19, by decide⟩).energy) (xi := (84246805599763 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12593 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12593]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12593])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12593) (a := (41708340223847 / 50000000000000 : ℝ)) (b := (163584486591 / 100000000000000 : ℝ)) (q := (566221597661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12593])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12593]

theorem cert12594_0 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (10509700954283 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264683698147 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨0, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (10509700954283 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264683698147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_1 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (84042598488263 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264687671231 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨1, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (84042598488263 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264687671231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_2 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (84007614324859 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264691705001 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨2, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (84007614324859 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264691705001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_3 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (41986327553721 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (18117565543 / 800000000000 : ℝ))
      (E := (cell12594 ⟨3, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (41986327553721 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (18117565543 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_4 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (41968860399799 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132349850751 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨4, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (41968860399799 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132349850751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_5 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83902811365103 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566175920383 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨5, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83902811365103 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566175920383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_6 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83867926767923 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566176924787 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨6, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83867926767923 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566176924787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_7 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (10479133371527 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (56617792611 / 2500000000000 : ℝ))
      (E := (cell12594 ⟨7, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (10479133371527 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (56617792611 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_8 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20949557985581 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132357852571 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨8, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20949557985581 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132357852571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_9 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (4188171082139 / 5000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132359825359 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨9, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (4188171082139 / 5000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132359825359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_10 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83728636038301 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264723664391 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨10, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83728636038301 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264723664391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_11 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83693875093787 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (45294553903 / 2000000000000 : ℝ))
      (E := (cell12594 ⟨11, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83693875093787 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (45294553903 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_12 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20914784693581 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264731691637 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨12, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20914784693581 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264731691637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_13 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (41812213522589 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264735660257 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨13, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (41812213522589 / 50000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264735660257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_14 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (20897434967949 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264739665297 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨14, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (20897434967949 / 25000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264739665297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_15 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (16711015443961 / 20000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132371827293 / 50000000000000 : ℝ))
      (E := (cell12594 ⟨15, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (16711015443961 / 20000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (1132371827293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_16 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (83520439055013 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264747691963 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨16, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (83520439055013 / 100000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264747691963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_17 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (417429126717 / 500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264751666527 / 100000000000000 : ℝ))
      (E := (cell12594 ⟨17, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (417429126717 / 500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (2264751666527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_18 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (10431404506391 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566188910401 / 25000000000000 : ℝ))
      (E := (cell12594 ⟨18, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (10431404506391 / 12500000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (566188910401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12594_19 : CellCertificate 12594 (444837887072297 / 5000000000000000 : ℝ) (1667816962819327 / 1000000000000000000 : ℝ) (13478391962767 / 400000000000000 : ℝ)
    (cell12594 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · norm_num [cell12594]
  · have h := gap_lower (n := 12594) (a := (8341667114453 / 10000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (283094960047 / 12500000000000 : ℝ))
      (E := (cell12594 ⟨19, by decide⟩).energy) (xi := (13478391962767 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12594 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12594]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12594])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12594) (a := (8341667114453 / 10000000000000 : ℝ)) (b := (32714267193 / 20000000000000 : ℝ)) (q := (283094960047 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12594])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12594]

theorem cert12595_0 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (84077592250133 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264556981039 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨0, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (84077592250133 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264556981039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_1 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (84042583428353 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452912194363 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨1, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (84042583428353 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452912194363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_2 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (84007599588711 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264564966211 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨2, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (84007599588711 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264564966211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_3 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83972640694599 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132284486657 / 50000000000000 : ℝ))
      (E := (cell12595 ⟨3, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83972640694599 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (1132284486657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_4 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41968853354801 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566143250487 / 25000000000000 : ℝ))
      (E := (cell12595 ⟨4, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41968853354801 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566143250487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_5 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41951398798749 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264577002763 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨5, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41951398798749 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264577002763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_6 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41933956661127 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264580984001 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨6, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41933956661127 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264580984001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_7 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83833053848029 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (283073126451 / 12500000000000 : ℝ))
      (E := (cell12595 ⟨7, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83833053848029 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (283073126451 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_8 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41899109569583 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264588977411 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨8, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41899109569583 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264588977411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_9 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (418817045801 / 500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566148251209 / 25000000000000 : ℝ))
      (E := (cell12595 ⟨9, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (418817045801 / 500000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566148251209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_10 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (41864311937923 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264596985113 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨10, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (41864311937923 / 50000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264596985113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_11 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83693863251009 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264600983197 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨11, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83693863251009 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264600983197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_12 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (20914781812693 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264605005817 / 100000000000000 : ℝ))
      (E := (cell12595 ⟨12, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (20914781812693 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (2264605005817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_13 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (20906103960101 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (113230450067 / 5000000000000 : ℝ))
      (E := (cell12595 ⟨13, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (20906103960101 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (113230450067 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_14 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83589728985353 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566153243981 / 25000000000000 : ℝ))
      (E := (cell12595 ⟨14, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83589728985353 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566153243981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_15 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (5222191665703 / 6250000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566154248407 / 25000000000000 : ℝ))
      (E := (cell12595 ⟨15, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (5222191665703 / 6250000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566154248407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_16 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (16704085760779 / 20000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452924200403 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨16, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (16704085760779 / 20000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452924200403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_17 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83485815409277 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566156237077 / 25000000000000 : ℝ))
      (E := (cell12595 ⟨17, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83485815409277 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (566156237077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_18 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (20862806608389 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452925790811 / 20000000000000 : ℝ))
      (E := (cell12595 ⟨18, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (20862806608389 / 25000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (452925790811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12595_19 : CellCertificate 12595 (889647386102039 / 10000000000000000 : ℝ) (416921124986363 / 250000000000000000 : ℝ) (84233095068579 / 2500000000000000 : ℝ)
    (cell12595 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · norm_num [cell12595]
  · have h := gap_lower (n := 12595) (a := (83416661843067 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (17692445047 / 781250000000 : ℝ))
      (E := (cell12595 ⟨19, by decide⟩).energy) (xi := (84233095068579 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12595 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12595]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12595])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12595) (a := (83416661843067 / 100000000000000 : ℝ)) (b := (163558187471 / 100000000000000 : ℝ)) (q := (17692445047 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12595])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12595]

theorem cert12596_0 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (2627424277139 / 3125000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (3623088507 / 160000000000 : ℝ))
      (E := (cell12596 ⟨0, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (2627424277139 / 3125000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (3623088507 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_1 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (1680851367417 / 2000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132217162703 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨1, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (1680851367417 / 2000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132217162703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_2 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (8400758485493 / 10000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (113221916917 / 5000000000000 : ℝ))
      (E := (cell12596 ⟨2, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (8400758485493 / 10000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (113221916917 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_3 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41986313142041 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264442364759 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨3, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41986313142041 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264442364759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_4 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (83937692621893 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132223177797 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨4, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (83937692621893 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132223177797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_5 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (4195139191607 / 5000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132225159671 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨5, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (4195139191607 / 5000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132225159671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_6 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (83867899878793 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132227161091 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨6, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (83867899878793 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132227161091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_7 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (8383304072601 / 10000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566114578551 / 25000000000000 : ℝ))
      (E := (cell12596 ⟨7, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (8383304072601 / 10000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566114578551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_8 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41899103169069 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (70764446973 / 3125000000000 : ℝ))
      (E := (cell12596 ⟨8, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41899103169069 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (70764446973 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_9 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (83763396679709 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452893270893 / 20000000000000 : ℝ))
      (E := (cell12596 ⟨9, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (83763396679709 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452893270893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_10 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41864305857721 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264470301383 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨10, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41864305857721 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264470301383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_11 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (83693851410241 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264474324893 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨11, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (83693851410241 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264474324893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_12 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (10457389466149 / 12500000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264478315627 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨12, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (10457389466149 / 12500000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264478315627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_13 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20906101159391 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566120584523 / 25000000000000 : ℝ))
      (E := (cell12596 ⟨13, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20906101159391 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (566120584523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_14 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (16717943620161 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264486340387 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨14, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (16717943620161 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264486340387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_15 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (41777528042273 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264490328421 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨15, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (41777528042273 / 50000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264490328421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_16 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (83520418554593 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264494307857 / 100000000000000 : ℝ))
      (E := (cell12596 ⟨16, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (83520418554593 / 100000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (2264494307857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_17 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20871451369233 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132249171157 / 50000000000000 : ℝ))
      (E := (cell12596 ⟨17, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20871451369233 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (1132249171157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_18 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (20862804204431 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452900464119 / 20000000000000 : ℝ))
      (E := (cell12596 ⟨18, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (20862804204431 / 25000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (452900464119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12596_19 : CellCertificate 12596 (889619002390949 / 10000000000000000 : ℝ) (1667552058111077 / 1000000000000000000 : ℝ) (168452483006621 / 5000000000000000 : ℝ)
    (cell12596 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · norm_num [cell12596]
  · have h := gap_lower (n := 12596) (a := (16683330508661 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (141531644113 / 6250000000000 : ℝ))
      (E := (cell12596 ⟨19, by decide⟩).energy) (xi := (168452483006621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12596 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12596]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12596])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12596) (a := (16683330508661 / 20000000000000 : ℝ)) (b := (163545041109 / 100000000000000 : ℝ)) (q := (141531644113 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12596])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12596]

theorem cert12597_0 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (84077561489209 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (283037963207 / 12500000000000 : ℝ))
      (E := (cell12597 ⟨0, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (84077561489209 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (283037963207 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_1 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (10505319164469 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (283038466501 / 12500000000000 : ℝ))
      (E := (cell12597 ⟨1, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (10505319164469 / 12500000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (283038466501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_2 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (16801514024703 / 20000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452862341139 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨2, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (16801514024703 / 20000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452862341139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_3 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (20993152968973 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264315751471 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨3, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (20993152968973 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264315751471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_4 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (8393767853647 / 10000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (45286394091 / 2000000000000 : ℝ))
      (E := (cell12597 ⟨4, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (8393767853647 / 10000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (45286394091 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_5 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (83902770069029 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452864749421 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨5, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (83902770069029 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452864749421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_6 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (4193394321877 / 5000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264327713693 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨6, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (4193394321877 / 5000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264327713693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_7 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (1047912845077 / 1250000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264331728157 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨7, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (1047912845077 / 1250000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264331728157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_8 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41899096769619 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132167870153 / 50000000000000 : ℝ))
      (E := (cell12597 ⟨8, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41899096769619 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (1132167870153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_9 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (83763384201307 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452867939921 / 20000000000000 : ℝ))
      (E := (cell12597 ⟨9, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (83763384201307 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (452867939921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_10 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (2616518736159 / 3125000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264343729273 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨10, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (2616518736159 / 3125000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264343729273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_11 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (16738767914297 / 20000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264347720237 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨11, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (16738767914297 / 20000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264347720237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_12 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (5228694013099 / 6250000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264351737231 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨12, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (5228694013099 / 6250000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264351737231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_13 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (5226524589791 / 6250000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264355728621 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨13, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (5226524589791 / 6250000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264355728621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_14 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (83589707218151 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264359700563 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨14, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (83589707218151 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264359700563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_15 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (83555045519699 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (566090929279 / 25000000000000 : ℝ))
      (E := (cell12597 ⟨15, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (83555045519699 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (566090929279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_16 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (20880102076777 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264367725839 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨16, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (20880102076777 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264367725839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_17 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (20871448886591 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (283046466519 / 12500000000000 : ℝ))
      (E := (cell12597 ⟨17, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (20871448886591 / 25000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (283046466519 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_18 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (83451207203629 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (35380870047 / 1562500000000 : ℝ))
      (E := (cell12597 ⟨18, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (83451207203629 / 100000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (35380870047 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12597_19 : CellCertificate 12597 (177918124602057 / 2000000000000000 : ℝ) (1667419637311191 / 1000000000000000000 : ℝ) (336877556284719 / 10000000000000000 : ℝ)
    (cell12597 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · norm_num [cell12597]
  · have h := gap_lower (n := 12597) (a := (41708321622621 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264379699757 / 100000000000000 : ℝ))
      (E := (cell12597 ⟨19, by decide⟩).energy) (xi := (336877556284719 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12597 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12597]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12597])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12597) (a := (41708321622621 / 50000000000000 : ℝ)) (b := (163531896877 / 100000000000000 : ℝ)) (q := (2264379699757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12597])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12597]

theorem cert12598_0 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (42038773056207 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (283022143423 / 12500000000000 : ℝ))
      (E := (cell12598 ⟨0, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (42038773056207 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (283022143423 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_1 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (84042538263059 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132090566899 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨1, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (84042538263059 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132090566899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_2 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (16801511078893 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264185126127 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨2, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (16801511078893 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264185126127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_3 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83972597470027 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132094566727 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨3, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83972597470027 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132094566727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_4 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83937664453333 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132096582301 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨4, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83937664453333 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132096582301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_5 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (16780551261633 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264197170217 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨5, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (16780551261633 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264197170217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_6 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83867872998493 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264201158537 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨6, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83867872998493 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264201158537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_7 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83833014488477 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264205137543 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨7, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83833014488477 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264205137543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_8 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41899090371233 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264209172949 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨8, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41899090371233 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264209172949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_9 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (16752674344999 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132106578139 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨9, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (16752674344999 / 20000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132106578139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_10 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (5233036712549 / 6250000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452843430543 / 20000000000000 : ℝ))
      (E := (cell12598 ⟨10, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (5233036712549 / 6250000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452843430543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_11 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83693827734739 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (141513823077 / 6250000000000 : ℝ))
      (E := (cell12598 ⟨11, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83693827734739 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (141513823077 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_12 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (20914773172987 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264225154467 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨12, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (20914773172987 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264225154467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_13 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83624382237681 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132114557411 / 50000000000000 : ℝ))
      (E := (cell12598 ⟨13, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83624382237681 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (1132114557411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_14 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (8358969633739 / 10000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264233114579 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨14, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (8358969633739 / 10000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264233114579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_15 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41777517478353 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566059289929 / 25000000000000 : ℝ))
      (E := (cell12598 ⟨15, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41777517478353 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (566059289929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_16 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41760199030719 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452848227923 / 20000000000000 : ℝ))
      (E := (cell12598 ⟨16, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41760199030719 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452848227923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_17 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (20871446404393 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264245117823 / 100000000000000 : ℝ))
      (E := (cell12598 ⟨17, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (20871446404393 / 25000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (2264245117823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_18 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (83451197591273 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452849831547 / 20000000000000 : ℝ))
      (E := (cell12598 ⟨18, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (83451197591273 / 100000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (452849831547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12598_19 : CellCertificate 12598 (27798820248719 / 312500000000000 : ℝ) (833643618770391 / 500000000000000000 : ℝ) (84212537771879 / 2500000000000000 : ℝ)
    (cell12598 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · norm_num [cell12598]
  · have h := gap_lower (n := 12598) (a := (41708316974439 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (283031643483 / 12500000000000 : ℝ))
      (E := (cell12598 ⟨19, by decide⟩).energy) (xi := (84212537771879 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12598 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12598]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12598])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12598) (a := (41708316974439 / 50000000000000 : ℝ)) (b := (6540750191 / 4000000000000 : ℝ)) (q := (283031643483 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12598])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12598]

theorem cert12599_0 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (84077530738063 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264050642061 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨0, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (84077530738063 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264050642061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_1 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (8404252321277 / 10000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264054646423 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨1, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (8404252321277 / 10000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264054646423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_2 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (84007540667779 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452811719927 / 20000000000000 : ℝ))
      (E := (cell12599 ⟨2, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (84007540667779 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452811719927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_3 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83972583066487 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264062626447 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨3, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83972583066487 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264062626447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_4 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41968825186241 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452813323993 / 20000000000000 : ℝ))
      (E := (cell12599 ⟨4, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41968825186241 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452813323993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_5 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83902742549547 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132035323299 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨5, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83902742549547 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132035323299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_6 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83867859561653 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264074598771 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨6, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83867859561653 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264074598771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_7 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41916500686481 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264078600323 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨7, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41916500686481 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264078600323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_8 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83798167947823 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264082601063 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨8, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83798167947823 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264082601063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_9 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83763359250771 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (141505413029 / 6250000000000 : ℝ))
      (E := (cell12599 ⟨9, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83763359250771 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (141505413029 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_10 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (8372857524653 / 10000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (141505664359 / 6250000000000 : ℝ))
      (E := (cell12599 ⟨10, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (8372857524653 / 10000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (141505664359 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_11 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (20923453975001 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264094613819 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨11, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (20923453975001 / 25000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264094613819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_12 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83659081176283 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264098625417 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨12, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83659081176283 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264098625417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_13 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41812185520319 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452820522581 / 20000000000000 : ℝ))
      (E := (cell12599 ⟨13, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41812185520319 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (452820522581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_14 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83589685458523 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566026645609 / 25000000000000 : ℝ))
      (E := (cell12599 ⟨14, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83589685458523 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (566026645609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_15 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83555024395567 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264110598069 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨15, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83555024395567 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264110598069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_16 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83520387817583 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132057303679 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨16, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83520387817583 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132057303679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_17 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (83485775690557 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264118615723 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨17, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (83485775690557 / 100000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264118615723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_18 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (16690237596131 / 20000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132061314167 / 50000000000000 : ℝ))
      (E := (cell12599 ⟨18, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (16690237596131 / 20000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (1132061314167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

theorem cert12599_19 : CellCertificate 12599 (889533877236081 / 10000000000000000 : ℝ) (1667154858794841 / 1000000000000000000 : ℝ) (336822750420401 / 10000000000000000 : ℝ)
    (cell12599 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · norm_num [cell12599]
  · have h := gap_lower (n := 12599) (a := (41708312327107 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264126591881 / 100000000000000 : ℝ))
      (E := (cell12599 ⟨19, by decide⟩).energy) (xi := (336822750420401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12599 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12599]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12599])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12599) (a := (41708312327107 / 50000000000000 : ℝ)) (b := (163505614803 / 100000000000000 : ℝ)) (q := (2264126591881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12599])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12599]

end BstLean.Part268
