import BstLean.Part268CellShard16Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12750_0 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (84075236923057 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245375203569 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨0, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (84075236923057 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245375203569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_1 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (16808055575907 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245379222769 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨1, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (16808055575907 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245379222769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_2 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (42002671873863 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122691594767 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨2, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (42002671873863 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122691594767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_3 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83970434491179 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245387228357 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨3, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83970434491179 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245387228357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_4 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41967775036817 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245391174119 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨4, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41967775036817 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245391174119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_5 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41950345229511 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245395208757 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨5, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41950345229511 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245395208757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_6 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83865855611463 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (561349806113 / 25000000000000 : ℝ))
      (E := (cell12750 ⟨6, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83865855611463 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (561349806113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_7 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41915522747633 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280675403613 / 12500000000000 : ℝ))
      (E := (cell12750 ⟨7, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41915522747633 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280675403613 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_8 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83796260074927 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122703614779 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨8, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83796260074927 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122703614779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_9 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41880749657563 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280676404201 / 12500000000000 : ℝ))
      (E := (cell12750 ⟨9, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41880749657563 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280676404201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_10 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83726763180731 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122707594973 / 50000000000000 : ℝ))
      (E := (cell12750 ⟨10, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83726763180731 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (1122707594973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_11 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (8369205163679 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245419221339 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨11, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (8369205163679 / 10000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245419221339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_12 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (10457170581067 / 12500000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245423218107 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨12, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (10457170581067 / 12500000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245423218107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_13 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (4181135109069 / 5000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245427186377 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨13, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (4181135109069 / 5000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245427186377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_14 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20897016050229 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280678898771 / 12500000000000 : ℝ))
      (E := (cell12750 ⟨14, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20897016050229 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280678898771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_15 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (16710690134583 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (140339702199 / 6250000000000 : ℝ))
      (E := (cell12750 ⟨15, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (16710690134583 / 20000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (140339702199 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_16 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (41759430781663 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280679901313 / 12500000000000 : ℝ))
      (E := (cell12750 ⟨16, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (41759430781663 / 50000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (280679901313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_17 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83484296838273 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245443237629 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨17, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83484296838273 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245443237629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_18 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (83449756464059 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245447205057 / 100000000000000 : ℝ))
      (E := (cell12750 ⟨18, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (83449756464059 / 100000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (2245447205057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12750_19 : CellCertificate 12750 (885298970126629 / 10000000000000000 : ℝ) (164740404868793 / 100000000000000000 : ℝ) (332736528762233 / 10000000000000000 : ℝ)
    (cell12750 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · norm_num [cell12750]
  · have h := gap_lower (n := 12750) (a := (20853810101789 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (22454512339 / 1000000000000 : ℝ))
      (E := (cell12750 ⟨19, by decide⟩).energy) (xi := (332736528762233 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12750 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12750]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12750])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12750) (a := (20853810101789 / 25000000000000 : ℝ)) (b := (6461824219 / 4000000000000 : ℝ)) (q := (22454512339 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12750])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12750]

theorem cert12751_0 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (84075221913547 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (89810166431 / 4000000000000 : ℝ))
      (E := (cell12751 ⟨0, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (84075221913547 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (89810166431 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_1 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (10505032898517 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (22452581487 / 1000000000000 : ℝ))
      (E := (cell12751 ⟨1, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (10505032898517 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (22452581487 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_2 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (84005329373989 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (89810485711 / 4000000000000 : ℝ))
      (E := (cell12751 ⟨2, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (84005329373989 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (89810485711 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_3 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (16794084086931 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122633075897 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨3, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (16794084086931 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122633075897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_4 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (671484290671 / 800000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245270126383 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨4, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (671484290671 / 800000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245270126383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_5 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83900677035581 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561318533171 / 25000000000000 : ℝ))
      (E := (cell12751 ⟨5, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83900677035581 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561318533171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_6 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (16773168500779 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245278178719 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨6, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (16773168500779 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245278178719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_7 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41915516351563 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245282156297 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨7, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41915516351563 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245282156297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_8 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (8379624759777 / 10000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122643065399 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨8, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (8379624759777 / 10000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122643065399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_9 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83761487152511 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245290167437 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨9, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83761487152511 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245290167437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_10 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41863375666107 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245294157129 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨10, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41863375666107 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245294157129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_11 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83692040101931 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122649082283 / 50000000000000 : ℝ))
      (E := (cell12751 ⟨11, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83692040101931 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (1122649082283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_12 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (16731470685379 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561325534523 / 25000000000000 : ℝ))
      (E := (cell12751 ⟨12, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (16731470685379 / 20000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561325534523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_13 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41811345636259 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (449061228391 / 20000000000000 : ℝ))
      (E := (cell12751 ⟨13, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41811345636259 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (449061228391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_14 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (41794026802197 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245310182099 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨14, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (41794026802197 / 50000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245310182099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_15 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (10444180048537 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (449062829579 / 20000000000000 : ℝ))
      (E := (cell12751 ⟨15, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (10444180048537 / 12500000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (449062829579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_16 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83518851590173 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245318161039 / 100000000000000 : ℝ))
      (E := (cell12751 ⟨16, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83518851590173 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (2245318161039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_17 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (83484287176151 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561330542133 / 25000000000000 : ℝ))
      (E := (cell12751 ⟨17, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (83484287176151 / 100000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561330542133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_18 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (20862436778133 / 25000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561331543819 / 25000000000000 : ℝ))
      (E := (cell12751 ⟨18, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (20862436778133 / 25000000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (561331543819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12751_19 : CellCertificate 12751 (442635622719861 / 5000000000000000 : ℝ) (823637404175571 / 500000000000000000 : ℝ) (332709802679853 / 10000000000000000 : ℝ)
    (cell12751 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · norm_num [cell12751]
  · have h := gap_lower (n := 12751) (a := (2606725980181 / 3125000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224533018593 / 10000000000000 : ℝ))
      (E := (cell12751 ⟨19, by decide⟩).energy) (xi := (332709802679853 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12751 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12751]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12751])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12751) (a := (2606725980181 / 3125000000000 : ℝ)) (b := (40383195753 / 25000000000000 : ℝ)) (q := (224533018593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12751])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12751]

theorem cert12752_0 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (16815041381279 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245133113317 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨0, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (16815041381279 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245133113317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_1 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (5252515531191 / 6250000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122568563923 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨1, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (5252515531191 / 6250000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122568563923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_2 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (21001328750633 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (449028229859 / 20000000000000 : ℝ))
      (E := (cell12752 ⟨2, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (21001328750633 / 25000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (449028229859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_3 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83970406380373 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245145128571 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨3, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83970406380373 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245145128571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_4 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83935522596319 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245149132051 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨4, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83935522596319 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245149132051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_5 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41950331807153 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245153110077 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨5, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41950331807153 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245153110077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_6 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41932914699227 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245157128559 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨6, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41932914699227 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245157128559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_7 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41915509956537 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (561290284321 / 25000000000000 : ℝ))
      (E := (cell12752 ⟨7, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41915509956537 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (561290284321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_8 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (10474529390333 / 12500000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (449033028739 / 20000000000000 : ℝ))
      (E := (cell12752 ⟨8, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (10474529390333 / 12500000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (449033028739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_9 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83761474991907 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (280646144373 / 12500000000000 : ℝ))
      (E := (cell12752 ⟨9, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83761474991907 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (280646144373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_10 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83726739485671 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245173120043 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨10, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83726739485671 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245173120043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_11 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (5230751785563 / 6250000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (449035432327 / 20000000000000 : ℝ))
      (E := (cell12752 ⟨11, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (5230751785563 / 6250000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (449035432327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_12 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83657342207151 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (14032382313 / 625000000000 : ℝ))
      (E := (cell12752 ⟨12, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83657342207151 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (14032382313 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_13 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (16724536073103 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (4490370303 / 200000000000 : ℝ))
      (E := (cell12752 ⟨13, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (16724536073103 / 20000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (4490370303 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_14 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41794021504847 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245189169917 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨14, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41794021504847 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245189169917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_15 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83553430105461 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245193172863 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨15, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83553430105461 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245193172863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_16 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41759420809383 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (70162411429 / 3125000000000 : ℝ))
      (E := (cell12752 ⟨16, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41759420809383 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (70162411429 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_17 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41742138757869 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245201153651 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨17, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41742138757869 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245201153651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_18 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (41724868881339 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122602570767 / 50000000000000 : ℝ))
      (E := (cell12752 ⟨18, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (41724868881339 / 50000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (1122602570767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12752_19 : CellCertificate 12752 (885243524926223 / 10000000000000000 : ℝ) (411786397072701 / 250000000000000000 : ℝ) (166341540472813 / 5000000000000000 : ℝ)
    (cell12752 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · norm_num [cell12752]
  · have h := gap_lower (n := 12752) (a := (83415222326063 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245209134037 / 100000000000000 : ℝ))
      (E := (cell12752 ⟨19, by decide⟩).energy) (xi := (166341540472813 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12752 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12752]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12752])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12752) (a := (83415222326063 / 100000000000000 : ℝ)) (b := (80759981299 / 50000000000000 : ℝ)) (q := (2245209134037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12752])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12752]

theorem cert12753_0 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (42037595950799 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449002423803 / 20000000000000 : ℝ))
      (E := (cell12753 ⟨0, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (42037595950799 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449002423803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_1 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (42020116906147 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245016160209 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨1, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (42020116906147 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245016160209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_2 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (16801060126671 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (35078439863 / 1562500000000 : ℝ))
      (E := (cell12753 ⟨2, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (16801060126671 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (35078439863 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_3 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83970392328331 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561256039673 / 25000000000000 : ℝ))
      (E := (cell12753 ⟨3, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83970392328331 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (561256039673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_4 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83935508860967 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122514066607 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨4, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83935508860967 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122514066607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_5 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41950325097597 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (112251607047 / 5000000000000 : ℝ))
      (E := (cell12753 ⟨5, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41950325097597 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (112251607047 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_6 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41932908147569 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (224503613193 / 10000000000000 : ℝ))
      (E := (cell12753 ⟨6, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41932908147569 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (224503613193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_7 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (8383100712511 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245040171863 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨7, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (8383100712511 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245040171863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_8 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83796222649607 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449008830449 / 20000000000000 : ℝ))
      (E := (cell12753 ⟨8, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83796222649607 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (449008830449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_9 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (16752292566663 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245048138223 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨9, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (16752292566663 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245048138223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_10 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41863363820551 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245052136737 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨10, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41863363820551 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245052136737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_11 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83692017038021 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245056154473 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨11, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83692017038021 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245056154473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_12 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (41828665494653 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122530069889 / 50000000000000 : ℝ))
      (E := (cell12753 ⟨12, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (41828665494653 / 50000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (1122530069889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_13 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83622669460373 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245064156893 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨13, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83622669460373 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245064156893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_14 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (5224252026051 / 6250000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245068153621 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨14, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (5224252026051 / 6250000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245068153621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_15 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (8355341982441 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245072135591 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨15, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (8355341982441 / 10000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245072135591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_16 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (83518831649107 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245076166379 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨16, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (83518831649107 / 100000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245076166379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_17 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (16696853571407 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280635024123 / 12500000000000 : ℝ))
      (E := (cell12753 ⟨17, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (16696853571407 / 20000000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280635024123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_18 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (2607804012953 / 3125000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245084162069 / 100000000000000 : ℝ))
      (E := (cell12753 ⟨18, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (2607804012953 / 3125000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (2245084162069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12753_19 : CellCertificate 12753 (885215808585147 / 10000000000000000 : ℝ) (329403277700429 / 200000000000000000 : ℝ) (166328181779203 / 5000000000000000 : ℝ)
    (cell12753 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · norm_num [cell12753]
  · have h := gap_lower (n := 12753) (a := (2606725415249 / 3125000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280636024343 / 12500000000000 : ℝ))
      (E := (cell12753 ⟨19, by decide⟩).energy) (xi := (166328181779203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12753 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12753]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12753])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12753) (a := (2606725415249 / 3125000000000 : ℝ)) (b := (161507144233 / 100000000000000 : ℝ)) (q := (280636024343 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12753])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12753]

theorem cert12754_0 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (42037588449579 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244891177869 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨0, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (42037588449579 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244891177869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_1 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (1680804382557 / 2000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (140305949247 / 6250000000000 : ℝ))
      (E := (cell12754 ⟨1, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (1680804382557 / 2000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (140305949247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_2 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (10500660783307 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561224801613 / 25000000000000 : ℝ))
      (E := (cell12754 ⟨2, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (10500660783307 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561224801613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_3 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83970378278531 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (140306449017 / 6250000000000 : ℝ))
      (E := (cell12754 ⟨3, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83970378278531 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (140306449017 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_4 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (10491936890977 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244907187787 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨4, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (10491936890977 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244907187787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_5 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83900636778247 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244911167339 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨5, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83900636778247 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244911167339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_6 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83865803193949 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122457594417 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨6, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83865803193949 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122457594417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_7 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83830994339233 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244919202059 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨7, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83830994339233 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244919202059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_8 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (418981050893 / 500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122461607227 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨8, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (418981050893 / 500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122461607227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_9 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (16752290135347 / 20000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122463587591 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨9, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (16752290135347 / 20000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122463587591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_10 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83726715798507 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244931207213 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨10, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83726715798507 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244931207213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_11 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (8369200550897 / 10000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244935201157 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨11, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (8369200550897 / 10000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244935201157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_12 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41828659886679 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244939221481 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨12, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41828659886679 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244939221481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_13 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (8362265855709 / 10000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (448988643251 / 20000000000000 : ℝ))
      (E := (cell12754 ⟨13, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (8362265855709 / 10000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (448988643251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_14 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (522425136411 / 625000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561236797839 / 25000000000000 : ℝ))
      (E := (cell12754 ⟨14, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (522425136411 / 625000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (561236797839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_15 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (10444176193143 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122475605289 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨15, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (10444176193143 / 12500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122475605289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_16 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (41759410840597 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244955221187 / 100000000000000 : ℝ))
      (E := (cell12754 ⟨16, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (41759410840597 / 50000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (2244955221187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_17 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (2087106455001 / 2500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122479614161 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨17, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (2087106455001 / 2500000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122479614161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_18 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (5215607441749 / 6250000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122481618443 / 50000000000000 : ℝ))
      (E := (cell12754 ⟨18, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (5215607441749 / 6250000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (1122481618443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12754_19 : CellCertificate 12754 (55324256025969 / 625000000000000 : ℝ) (823443604490197 / 500000000000000000 : ℝ) (332629650517043 / 10000000000000000 : ℝ)
    (cell12754 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · norm_num [cell12754]
  · have h := gap_lower (n := 12754) (a := (83415204251507 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (280620899159 / 12500000000000 : ℝ))
      (E := (cell12754 ⟨19, by decide⟩).energy) (xi := (332629650517043 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12754 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12754]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12754])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12754) (a := (83415204251507 / 100000000000000 : ℝ)) (b := (32298865583 / 20000000000000 : ℝ)) (q := (280620899159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12754])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12754]

theorem cert12755_0 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (84075161899073 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (56119257247 / 2500000000000 : ℝ))
      (E := (cell12755 ⟨0, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (84075161899073 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (56119257247 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_1 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (42020102222861 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (448954853783 / 20000000000000 : ℝ))
      (E := (cell12755 ⟨1, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (42020102222861 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (448954853783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_2 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (84005271901837 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (224477825709 / 10000000000000 : ℝ))
      (E := (cell12755 ⟨2, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (84005271901837 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (224477825709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_3 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (8397036423097 / 10000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244782263197 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨3, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (8397036423097 / 10000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244782263197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_4 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83935481396867 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244786295767 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨4, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83935481396867 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244786295767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_5 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83900623363463 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244790247209 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨5, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83900623363463 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244790247209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_6 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20966447523721 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (280599287409 / 12500000000000 : ℝ))
      (E := (cell12755 ⟨6, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20966447523721 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (280599287409 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_7 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20957745388861 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244798285849 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨7, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20957745388861 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244798285849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_8 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41898098854821 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244802272317 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨8, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41898098854821 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244802272317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_9 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (16752287704433 / 20000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122403132931 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨9, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (16752287704433 / 20000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122403132931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_10 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20931675989471 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244810273423 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨10, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20931675989471 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244810273423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_11 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83691993981853 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122407150843 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨11, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83691993981853 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122407150843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_12 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (20914327139827 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122409149497 / 50000000000000 : ℝ))
      (E := (cell12755 ⟨12, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (20914327139827 / 25000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (1122409149497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_13 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (41811323827833 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (561205567867 / 25000000000000 : ℝ))
      (E := (cell12755 ⟨13, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (41811323827833 / 50000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (561205567867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_14 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (3343520449461 / 4000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (561206570781 / 25000000000000 : ℝ))
      (E := (cell12755 ⟨14, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (3343520449461 / 4000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (561206570781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_15 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83553399267661 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244830281493 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨15, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83553399267661 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244830281493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_16 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83518811715027 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (56120856799 / 2500000000000 : ℝ))
      (E := (cell12755 ⟨16, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83518811715027 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (56120856799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_17 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83484248544753 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (448967651933 / 20000000000000 : ℝ))
      (E := (cell12755 ⟨17, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83484248544753 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (448967651933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_18 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (10431213715393 / 12500000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (70151322117 / 3125000000000 : ℝ))
      (E := (cell12755 ⟨18, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (10431213715393 / 12500000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (70151322117 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12755_19 : CellCertificate 12755 (885160388416309 / 10000000000000000 : ℝ) (1646758049720783 / 1000000000000000000 : ℝ) (41575367727549 / 1250000000000000 : ℝ)
    (cell12755 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · norm_num [cell12755]
  · have h := gap_lower (n := 12755) (a := (83415195216679 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244846304401 / 100000000000000 : ℝ))
      (E := (cell12755 ⟨19, by decide⟩).energy) (xi := (41575367727549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12755 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12755]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12755])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12755) (a := (83415195216679 / 100000000000000 : ℝ)) (b := (32296302729 / 20000000000000 : ℝ)) (q := (2244846304401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12755])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12755]

theorem cert12756_0 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (84075146901343 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244649397233 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨0, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (84075146901343 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244649397233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_1 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (84040189765911 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244653403099 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨1, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (84040189765911 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244653403099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_2 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (16801051507899 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244657361013 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨2, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (16801051507899 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244657361013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_3 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83970350185649 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561165348867 / 25000000000000 : ℝ))
      (E := (cell12756 ⟨3, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83970350185649 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (561165348867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_4 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83935467668119 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244665399247 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨4, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83935467668119 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244665399247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_5 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41950304975421 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280583672569 / 12500000000000 : ℝ))
      (E := (cell12756 ⟨5, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41950304975421 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280583672569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_6 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (16773155399589 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244673405287 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨6, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (16773155399589 / 20000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244673405287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_7 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83830968773741 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122338682629 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨7, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83830968773741 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122338682629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_8 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (20949046310683 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (14029258649 / 625000000000 : ℝ))
      (E := (cell12756 ⟨8, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (20949046310683 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (14029258649 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_9 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41880713184803 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280585676283 / 12500000000000 : ℝ))
      (E := (cell12756 ⟨9, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41880713184803 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (280585676283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_10 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83726692119233 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122344696709 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨10, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83726692119233 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122344696709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_11 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (8369198245667 / 10000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (224469339799 / 10000000000000 : ℝ))
      (E := (cell12756 ⟨11, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (8369198245667 / 10000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (224469339799 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_12 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83657297347153 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244697372321 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨12, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83657297347153 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244697372321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_13 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (83622636756101 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244701380651 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨13, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (83622636756101 / 100000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244701380651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_14 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (10448500081139 / 12500000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (112235268539 / 5000000000000 : ℝ))
      (E := (cell12756 ⟨14, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (10448500081139 / 12500000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (112235268539 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_15 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41776694495981 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244709406503 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨15, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41776694495981 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244709406503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_16 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41759400875303 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244713376891 / 100000000000000 : ℝ))
      (E := (cell12756 ⟨16, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41759400875303 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (2244713376891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_17 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (3339369555647 / 4000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (28058967543 / 1250000000000 : ℝ))
      (E := (cell12756 ⟨17, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (3339369555647 / 4000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (28058967543 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_18 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (41724850189987 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122360687323 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨18, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (41724850189987 / 50000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122360687323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12756_19 : CellCertificate 12756 (442566342293287 / 5000000000000000 : ℝ) (823314455359273 / 500000000000000000 : ℝ) (66515247493461 / 2000000000000000 : ℝ)
    (cell12756 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · norm_num [cell12756]
  · have h := gap_lower (n := 12756) (a := (20853796545871 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122362705807 / 50000000000000 : ℝ))
      (E := (cell12756 ⟨19, by decide⟩).energy) (xi := (66515247493461 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12756 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12756]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12756])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12756) (a := (20853796545871 / 25000000000000 : ℝ)) (b := (80734350711 / 50000000000000 : ℝ)) (q := (1122362705807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12756])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12756]

theorem cert12757_0 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (5254695744123 / 6250000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (224452849993 / 10000000000000 : ℝ))
      (E := (cell12757 ⟨0, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (5254695744123 / 6250000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (224452849993 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_1 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (16808035017683 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244532532667 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨1, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (16808035017683 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244532532667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_2 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (8400524317943 / 10000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122268259111 / 50000000000000 : ℝ))
      (E := (cell12757 ⟨2, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (8400524317943 / 10000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (1122268259111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_3 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41985168071283 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244540523203 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨3, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41985168071283 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244540523203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_4 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (20983863485393 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561136124557 / 25000000000000 : ℝ))
      (E := (cell12757 ⟨4, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (20983863485393 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561136124557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_5 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (83900596540383 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448909701887 / 20000000000000 : ℝ))
      (E := (cell12757 ⟨5, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (83900596540383 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448909701887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_6 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (83865763903129 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244552506883 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨6, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (83865763903129 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244552506883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_7 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (20957738998531 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448911299653 / 20000000000000 : ℝ))
      (E := (cell12757 ⟨7, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (20957738998531 / 25000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (448911299653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_8 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (8379617277787 / 10000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (70142517157 / 3125000000000 : ℝ))
      (E := (cell12757 ⟨8, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (8379617277787 / 10000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (70142517157 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_9 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (5235088388691 / 6250000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561141137591 / 25000000000000 : ℝ))
      (E := (cell12757 ⟨9, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (5235088388691 / 6250000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561141137591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_10 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (16745336056511 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561142127287 / 25000000000000 : ℝ))
      (E := (cell12757 ⟨10, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (16745336056511 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (561142127287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_11 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (83691970933421 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244572548141 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨11, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (83691970933421 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244572548141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_12 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (16731457227379 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244576499557 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨12, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (16731457227379 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244576499557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_13 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41811312929197 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (35071570997 / 1562500000000 : ℝ))
      (E := (cell12757 ⟨13, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41811312929197 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (35071570997 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_14 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (83587990063519 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (280573064059 / 12500000000000 : ℝ))
      (E := (cell12757 ⟨14, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (83587990063519 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (280573064059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_15 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (16710675743609 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244588527443 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨15, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (16710675743609 / 20000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244588527443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_16 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (8351879178793 / 10000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (112229626799 / 5000000000000 : ℝ))
      (E := (cell12757 ⟨16, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (8351879178793 / 10000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (112229626799 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_17 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (10435528654913 / 12500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244596543223 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨17, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (10435528654913 / 12500000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244596543223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_18 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (41724845519237 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244600554069 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨18, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (41724845519237 / 50000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244600554069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12757_19 : CellCertificate 12757 (6914882694729 / 78125000000000 : ℝ) (1646499791968917 / 1000000000000000000 : ℝ) (83137384364159 / 2500000000000000 : ℝ)
    (cell12757 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · norm_num [cell12757]
  · have h := gap_lower (n := 12757) (a := (83415177151921 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244604514911 / 100000000000000 : ℝ))
      (E := (cell12757 ⟨19, by decide⟩).energy) (xi := (83137384364159 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12757 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12757]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12757])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12757) (a := (83415177151921 / 100000000000000 : ℝ)) (b := (32291178249 / 20000000000000 : ℝ)) (q := (2244604514911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12757])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12757]

theorem cert12758_0 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (42037558456473 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561101928401 / 25000000000000 : ℝ))
      (E := (cell12758 ⟨0, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (42037558456473 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561101928401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_1 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16808032082647 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122205857729 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨1, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16808032082647 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122205857729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_2 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (42002614410821 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448883134171 / 20000000000000 : ℝ))
      (E := (cell12758 ⟨2, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (42002614410821 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (448883134171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_3 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83970322101723 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122209852143 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨3, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83970322101723 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122209852143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_4 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (10491930027153 / 12500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561105927133 / 25000000000000 : ℝ))
      (E := (cell12758 ⟨4, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (10491930027153 / 12500000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561105927133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_5 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83900583132087 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (140276730737 / 6250000000000 : ℝ))
      (E := (cell12758 ⟨5, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83900583132087 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (140276730737 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_6 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83865750810437 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561107929993 / 25000000000000 : ℝ))
      (E := (cell12758 ⟨6, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83865750810437 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561107929993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_7 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (5239433951037 / 6250000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244435684873 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨7, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (5239433951037 / 6250000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244435684873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_8 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16759232063011 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561109927467 / 25000000000000 : ℝ))
      (E := (cell12758 ⟨8, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16759232063011 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561109927467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_9 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (20940350517629 / 25000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244443686161 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨9, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (20940350517629 / 25000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244443686161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_10 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83726668447847 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122223839333 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨10, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83726668447847 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122223839333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_11 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (41845979706053 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561112923517 / 25000000000000 : ℝ))
      (E := (cell12758 ⟨11, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (41845979706053 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561112923517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_12 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (20914318732133 / 25000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122227840353 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨12, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (20914318732133 / 25000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122227840353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_13 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16724522992509 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244459702817 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨13, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16724522992509 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244459702817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_14 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (16717595895949 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (11222318541 / 500000000000 : ℝ))
      (E := (cell12758 ⟨14, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (16717595895949 / 20000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (11222318541 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_15 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83553368445911 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (28055846281 / 1250000000000 : ℝ))
      (E := (cell12758 ⟨15, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83553368445911 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (28055846281 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_16 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (41759390913499 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244471691039 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨16, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (41759390913499 / 50000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244471691039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_17 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (4174210979457 / 5000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561118934307 / 25000000000000 : ℝ))
      (E := (cell12758 ⟨17, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (4174210979457 / 5000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (561118934307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_18 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83449681698643 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122239864769 / 50000000000000 : ℝ))
      (E := (cell12758 ⟨18, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83449681698643 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (1122239864769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12758_19 : CellCertificate 12758 (442538644715769 / 5000000000000000 : ℝ) (411592673366783 / 250000000000000000 : ℝ) (332522841787239 / 10000000000000000 : ℝ)
    (cell12758 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · norm_num [cell12758]
  · have h := gap_lower (n := 12758) (a := (83415168121991 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244483730813 / 100000000000000 : ℝ))
      (E := (cell12758 ⟨19, by decide⟩).energy) (xi := (332522841787239 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12758 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12758]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12758])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12758) (a := (83415168121991 / 100000000000000 : ℝ)) (b := (80721541557 / 50000000000000 : ℝ)) (q := (2244483730813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12758])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12758]

theorem cert12759_0 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (84075101922277 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (280535858101 / 12500000000000 : ℝ))
      (E := (cell12759 ⟨0, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (84075101922277 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (280535858101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_1 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (8404014574037 / 10000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122145446817 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨1, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (8404014574037 / 10000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122145446817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_2 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (84005214466131 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (89771795071 / 4000000000000 : ℝ))
      (E := (cell12759 ⟨2, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (84005214466131 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (89771795071 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_3 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83970308063117 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122149440417 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨3, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83970308063117 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122149440417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_4 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83935426495077 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122151457169 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨4, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83935426495077 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122151457169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_5 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83900569725951 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244306869693 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨5, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83900569725951 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244306869693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_6 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (20966434429967 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (70134714709 / 3125000000000 : ℝ))
      (E := (cell12759 ⟨6, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (20966434429967 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (70134714709 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_7 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41915465220573 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244314867101 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨7, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41915465220573 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244314867101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_8 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (5237259240893 / 6250000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (3590910279 / 160000000000 : ℝ))
      (E := (cell12759 ⟨8, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (5237259240893 / 6250000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (3590910279 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_9 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (16752277984797 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (561080718921 / 25000000000000 : ℝ))
      (E := (cell12759 ⟨9, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (16752277984797 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (561080718921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_10 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83726656615111 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (561081725493 / 25000000000000 : ℝ))
      (E := (cell12759 ⟨10, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83726656615111 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (561081725493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_11 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (20922986973181 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122165446923 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨11, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (20922986973181 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122165446923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_12 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (16731452744413 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122167457883 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨12, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (16731452744413 / 20000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122167457883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_13 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41811302034277 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244338915801 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨13, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41811302034277 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244338915801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_14 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (326515503507 / 390625000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244342899821 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨14, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (326515503507 / 390625000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244342899821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_15 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41776679087779 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122173465809 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨15, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41776679087779 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122173465809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_16 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (83518771867811 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244350900259 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨16, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (83518771867811 / 100000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244350900259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_17 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41742104970341 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122177463621 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨17, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41742104970341 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122177463621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_18 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (41724836180241 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122179450527 / 50000000000000 : ℝ))
      (E := (cell12759 ⟨18, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (41724836180241 / 50000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (1122179450527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12759_19 : CellCertificate 12759 (442524799052133 / 5000000000000000 : ℝ) (1646241615208429 / 1000000000000000000 : ℝ) (332496150457969 / 10000000000000000 : ℝ)
    (cell12759 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · norm_num [cell12759]
  · have h := gap_lower (n := 12759) (a := (20853789773423 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244362942803 / 100000000000000 : ℝ))
      (E := (cell12759 ⟨19, by decide⟩).energy) (xi := (332496150457969 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12759 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12759]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12759])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12759) (a := (20853789773423 / 25000000000000 : ℝ)) (b := (40357569257 / 25000000000000 : ℝ)) (q := (2244362942803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12759])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12759]

theorem cert12760_0 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (84075086933961 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140260382937 / 6250000000000 : ℝ))
      (E := (cell12760 ⟨0, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (84075086933961 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140260382937 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_1 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (84040131069819 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244170125037 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨1, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (84040131069819 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244170125037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_2 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (16801040022579 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (448834827197 / 20000000000000 : ℝ))
      (E := (cell12760 ⟨2, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (16801040022579 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (448834827197 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_3 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (20992573506687 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122089055367 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨3, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (20992573506687 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122089055367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_4 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (10491926596891 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244182115651 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨4, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (10491926596891 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244182115651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_5 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (10487569540247 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140261631317 / 6250000000000 : ℝ))
      (E := (cell12760 ⟨5, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (10487569540247 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140261631317 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_6 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41932862315711 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244190132899 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨6, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41932862315711 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244190132899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_7 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (10478864708473 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244194102931 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨7, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (10478864708473 / 12500000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244194102931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_8 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41898067697783 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140262383409 / 6250000000000 : ℝ))
      (E := (cell12760 ⟨8, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41898067697783 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140262383409 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_9 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41880688889731 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122101059467 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨9, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41880688889731 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122101059467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_10 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (16745328956869 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244206121017 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨10, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (16745328956869 / 20000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244206121017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_11 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (41845968187637 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (89768405899 / 4000000000000 : ℝ))
      (E := (cell12760 ⟨11, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (41845968187637 / 50000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (89768405899 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_12 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (20914313129373 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561053536661 / 25000000000000 : ℝ))
      (E := (cell12760 ⟨12, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (20914313129373 / 25000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (561053536661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_13 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83622593176419 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122109062321 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨13, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83622593176419 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122109062321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_14 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83587958317657 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244222145481 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨14, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83587958317657 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244222145481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_15 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83553347906987 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140264134793 / 6250000000000 : ℝ))
      (E := (cell12760 ⟨15, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83553347906987 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (140264134793 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_16 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83518761910367 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122115081821 / 50000000000000 : ℝ))
      (E := (cell12760 ⟨16, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83518761910367 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (1122115081821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_17 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83484200293931 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (56105854287 / 2500000000000 : ℝ))
      (E := (cell12760 ⟨17, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83484200293931 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (56105854287 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_18 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (83449663023989 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244238126857 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨18, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (83449663023989 / 100000000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244238126857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12760_19 : CellCertificate 12760 (88502191094251 / 1000000000000000 : ℝ) (1646112557188047 / 1000000000000000000 : ℝ) (166234731733841 / 5000000000000000 : ℝ)
    (cell12760 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · norm_num [cell12760]
  · have h := gap_lower (n := 12760) (a := (5213446879189 / 6250000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244242150879 / 100000000000000 : ℝ))
      (E := (cell12760 ⟨19, by decide⟩).energy) (xi := (166234731733841 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12760 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12760]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12760])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12760) (a := (5213446879189 / 6250000000000 : ℝ)) (b := (161417472987 / 100000000000000 : ℝ)) (q := (2244242150879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12760])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12760]

theorem cert12761_0 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (84075071947997 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (89761815381 / 4000000000000 : ℝ))
      (E := (cell12761 ⟨0, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (84075071947997 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (89761815381 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_1 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (84040116401581 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244049409669 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨1, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (84040116401581 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244049409669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_2 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (42002592880967 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244053390623 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨2, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (42002592880967 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244053390623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_3 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83970279992617 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122028696993 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨3, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83970279992617 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122028696993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_4 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41967699528689 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122030685189 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨4, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41967699528689 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122030685189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_5 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41950271460081 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (280508173241 / 12500000000000 : ℝ))
      (E := (cell12761 ⟨5, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41950271460081 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (280508173241 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_6 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41932855772549 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122034695347 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨6, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41932855772549 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122034695347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_7 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (16766180979301 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244073392367 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨7, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (16766180979301 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244073392367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_8 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83796122938891 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122038699189 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨8, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83796122938891 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122038699189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_9 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83761365636947 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244081415913 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨9, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83761365636947 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244081415913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_10 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83726632955549 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244085393853 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨10, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83726632955549 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244085393853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_11 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83691924859757 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561022349221 / 25000000000000 : ℝ))
      (E := (cell12761 ⟨11, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83691924859757 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561022349221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_12 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83657241314813 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122046715719 / 50000000000000 : ℝ))
      (E := (cell12761 ⟨12, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83657241314813 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (1122046715719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_13 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (4181129114307 / 5000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (112204869373 / 5000000000000 : ℝ))
      (E := (cell12761 ⟨13, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (4181129114307 / 5000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (112204869373 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_14 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83587947739341 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561025346759 / 25000000000000 : ℝ))
      (E := (cell12761 ⟨14, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83587947739341 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (561025346759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_15 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83553337640197 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244105435859 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨15, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83553337640197 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244105435859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_16 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83518751954667 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244109422997 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨16, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83518751954667 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244109422997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_17 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (41742095324443 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244113411729 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨17, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (41742095324443 / 50000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244113411729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_18 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (16689930737833 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244117406947 / 100000000000000 : ℝ))
      (E := (cell12761 ⟨18, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (16689930737833 / 20000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (2244117406947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12761_19 : CellCertificate 12761 (176998845589057 / 2000000000000000 : ℝ) (822991759700613 / 500000000000000000 : ℝ) (166221390407617 / 5000000000000000 : ℝ)
    (cell12761 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · norm_num [cell12761]
  · have h := gap_lower (n := 12761) (a := (83415141041987 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (280515176663 / 12500000000000 : ℝ))
      (E := (cell12761 ⟨19, by decide⟩).energy) (xi := (166221390407617 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12761 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12761]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12761])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12761) (a := (83415141041987 / 100000000000000 : ℝ)) (b := (16140467099 / 10000000000000 : ℝ)) (q := (280515176663 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12761])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12761]

theorem cert12762_0 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (16815011392877 / 20000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243924695223 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨0, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (16815011392877 / 20000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243924695223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_1 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (10505012716957 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (224392868969 / 10000000000000 : ℝ))
      (E := (cell12762 ⟨1, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (10505012716957 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (224392868969 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_2 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (84005171413249 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243932698551 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨2, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (84005171413249 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243932698551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_3 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83970265960721 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (560984168177 / 25000000000000 : ℝ))
      (E := (cell12762 ⟨3, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83970265960721 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (560984168177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_4 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83935385341827 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1121970339261 / 50000000000000 : ℝ))
      (E := (cell12762 ⟨4, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83935385341827 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1121970339261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_5 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83900529520507 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243944666331 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨5, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83900529520507 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243944666331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_6 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (16773139692179 / 20000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243948702033 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨6, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (16773139692179 / 20000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243948702033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_7 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83830892127311 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (89758107097 / 4000000000000 : ℝ))
      (E := (cell12762 ⟨7, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83830892127311 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (89758107097 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_8 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83796110484261 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (56098917897 / 2500000000000 : ℝ))
      (E := (cell12762 ⟨8, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83796110484261 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (56098917897 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_9 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83761353496439 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1121980354297 / 50000000000000 : ℝ))
      (E := (cell12762 ⟨9, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83761353496439 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1121980354297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_10 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41863310564361 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243964720481 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨10, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41863310564361 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243964720481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_11 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83691913346171 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1121984350073 / 50000000000000 : ℝ))
      (E := (cell12762 ⟨11, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83691913346171 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1121984350073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_12 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (20914307528507 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (44879454241 / 2000000000000 : ℝ))
      (E := (cell12762 ⟨12, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (20914307528507 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (44879454241 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_13 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41811285698859 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (8765534001 / 390625000000 : ℝ))
      (E := (cell12762 ⟨13, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41811285698859 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (8765534001 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_14 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (20896984290711 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243980682631 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨14, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (20896984290711 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243980682631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_15 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (20888331843797 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448796942193 / 20000000000000 : ℝ))
      (E := (cell12762 ⟨15, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (20888331843797 / 25000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (448796942193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_16 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (8351874200071 / 10000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243988736517 / 100000000000000 : ℝ))
      (E := (cell12762 ⟨16, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (8351874200071 / 10000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (2243988736517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_17 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (41742090502773 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (560998176551 / 25000000000000 : ℝ))
      (E := (cell12762 ⟨17, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (41742090502773 / 50000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (560998176551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_18 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (10431205544501 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (89759869653 / 4000000000000 : ℝ))
      (E := (cell12762 ⟨18, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (10431205544501 / 12500000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (89759869653 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12762_19 : CellCertificate 12762 (442483274555803 / 5000000000000000 : ℝ) (1645854501843209 / 1000000000000000000 : ℝ) (8310402562487 / 250000000000000 : ℝ)
    (cell12762 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · norm_num [cell12762]
  · have h := gap_lower (n := 12762) (a := (83415132018581 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122000365039 / 50000000000000 : ℝ))
      (E := (cell12762 ⟨19, by decide⟩).energy) (xi := (8310402562487 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12762 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12762]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12762])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12762) (a := (83415132018581 / 100000000000000 : ℝ)) (b := (161391871037 / 100000000000000 : ℝ)) (q := (1122000365039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12762])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12762]

theorem cert12763_0 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (21018760495781 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280475500159 / 12500000000000 : ℝ))
      (E := (cell12763 ⟨0, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (21018760495781 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (280475500159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_1 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (16808017414409 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243808022939 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨1, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (16808017414409 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243808022939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_2 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (84005157066837 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (224381200191 / 10000000000000 : ℝ))
      (E := (cell12763 ⟨2, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (84005157066837 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (224381200191 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_3 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41985125965531 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (140238500299 / 6250000000000 : ℝ))
      (E := (cell12763 ⟨3, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41985125965531 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (140238500299 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_4 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (10491921453559 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121910020043 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨4, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (10491921453559 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121910020043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_5 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20975129030753 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (448764800043 / 20000000000000 : ℝ))
      (E := (cell12763 ⟨5, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20975129030753 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (448764800043 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_6 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41932842689407 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121914004479 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨6, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41932842689407 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121914004479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_7 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (83830879360199 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (224383201609 / 10000000000000 : ℝ))
      (E := (cell12763 ⟨7, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (83830879360199 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (224383201609 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_8 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20949024507919 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121918014523 / 50000000000000 : ℝ))
      (E := (cell12763 ⟨8, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20949024507919 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (1121918014523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_9 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41880670678969 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243840055007 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨9, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41880670678969 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243840055007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_10 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (10465826162983 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (560961010713 / 25000000000000 : ℝ))
      (E := (cell12763 ⟨10, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (10465826162983 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (560961010713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_11 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20922975458629 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (140240503579 / 6250000000000 : ℝ))
      (E := (cell12763 ⟨11, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20922975458629 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (140240503579 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_12 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (1307144045549 / 1562500000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (112192602329 / 5000000000000 : ℝ))
      (E := (cell12763 ⟨12, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (1307144045549 / 1562500000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (112192602329 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_13 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (83622560511151 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243856016911 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨13, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (83622560511151 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243856016911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_14 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (20896981647041 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (560965008067 / 25000000000000 : ℝ))
      (E := (cell12763 ⟨14, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (20896981647041 / 25000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (560965008067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_15 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (41776658555979 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243864040177 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨15, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (41776658555979 / 50000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243864040177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_16 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (16703746409699 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243868046011 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨16, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (16703746409699 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243868046011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_17 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (10435521420489 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243872054907 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨17, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (10435521420489 / 12500000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243872054907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_18 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (83449635024519 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (448775214351 / 20000000000000 : ℝ))
      (E := (cell12763 ⟨18, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (83449635024519 / 100000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (448775214351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12763_19 : CellCertificate 12763 (884938874440489 / 10000000000000000 : ℝ) (1645725504509239 / 1000000000000000000 : ℝ) (332389428519277 / 10000000000000000 : ℝ)
    (cell12763 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · norm_num [cell12763]
  · have h := gap_lower (n := 12763) (a := (16683024599361 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243880042943 / 100000000000000 : ℝ))
      (E := (cell12763 ⟨19, by decide⟩).energy) (xi := (332389428519277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12763 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12763]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12763])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12763) (a := (16683024599361 / 20000000000000 : ℝ)) (b := (161379073127 / 100000000000000 : ℝ)) (q := (2243880042943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12763])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12763]

theorem cert12764_0 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (84075027004213 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243683360491 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨0, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (84075027004213 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243683360491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_1 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (16808014482149 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243687351581 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨1, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (16808014482149 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243687351581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_2 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (84005142722699 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243691358563 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨2, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (84005142722699 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243691358563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_3 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83970237903637 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121847695109 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨3, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83970237903637 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121847695109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_4 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (16787071583463 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121849698579 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨4, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (16787071583463 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121849698579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_5 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (3356020109107 / 4000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121851693791 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨5, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (3356020109107 / 4000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121851693791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_6 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83865672298853 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243707369427 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨6, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83865672298853 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243707369427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_7 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (8383086659517 / 10000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121855704181 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨7, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (8383086659517 / 10000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121855704181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_8 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (16759217116227 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121857697941 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨8, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (16759217116227 / 20000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121857697941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_9 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (20940332305361 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560929849281 / 25000000000000 : ℝ))
      (E := (cell12764 ⟨9, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (20940332305361 / 25000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560929849281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_10 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (3349063899239 / 4000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121861680483 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨10, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (3349063899239 / 4000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121861680483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_11 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83691890324791 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121863705083 / 50000000000000 : ℝ))
      (E := (cell12764 ⟨11, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83691890324791 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (1121863705083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_12 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83657207718137 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243731376931 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨12, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83657207718137 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243731376931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_13 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83622549626439 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243735383547 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨13, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83622549626439 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243735383547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_14 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83587916015301 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560934844451 / 25000000000000 : ℝ))
      (E := (cell12764 ⟨14, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83587916015301 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (560934844451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_15 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83553306850509 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243743423491 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨15, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83553306850509 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243743423491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_16 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83518722098023 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280468426209 / 12500000000000 : ℝ))
      (E := (cell12764 ⟨16, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83518722098023 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280468426209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_17 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83484161723981 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280468924953 / 12500000000000 : ℝ))
      (E := (cell12764 ⟨17, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83484161723981 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (280468924953 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_18 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (83449625694697 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243755398237 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨18, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (83449625694697 / 100000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243755398237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12764_19 : CellCertificate 12764 (221227800982737 / 2500000000000000 : ℝ) (1645596527394561 / 1000000000000000000 : ℝ) (332362758873483 / 10000000000000000 : ℝ)
    (cell12764 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · norm_num [cell12764]
  · have h := gap_lower (n := 12764) (a := (41707556988329 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243759410161 / 100000000000000 : ℝ))
      (E := (cell12764 ⟨19, by decide⟩).energy) (xi := (332362758873483 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12764 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12764]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12764])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12764) (a := (41707556988329 / 50000000000000 : ℝ)) (b := (8068313863 / 5000000000000 : ℝ)) (q := (2243759410161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12764])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12764]

theorem cert12765_0 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (21018753006913 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243562772879 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨0, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (21018753006913 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243562772879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_1 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (21010014437939 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243566791297 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨1, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (21010014437939 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243566791297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_2 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (42002564190417 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (17527896629 / 781250000000 : ℝ))
      (E := (cell12765 ⟨2, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (42002564190417 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (17527896629 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_3 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (5248138992403 / 6250000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243574771123 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨3, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (5248138992403 / 6250000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243574771123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_4 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41967672104177 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121789374871 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨4, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41967672104177 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121789374871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_5 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83900489334497 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243582770497 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨5, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83900489334497 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243582770497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_6 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (20966414805253 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243586783443 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨6, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (20966414805253 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243586783443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_7 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83830853832223 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243590796263 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨7, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83830853832223 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243590796263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_8 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83796073132639 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448718951677 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨8, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83796073132639 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448718951677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_9 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (20940329271739 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121799396487 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨9, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (20940329271739 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121799396487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_10 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41863292830027 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121801395463 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨10, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41863292830027 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121801395463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_11 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83691878816997 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (44872135177 / 2000000000000 : ℝ))
      (E := (cell12765 ⟨11, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83691878816997 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (44872135177 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_12 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83657196523031 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121805380601 / 50000000000000 : ℝ))
      (E := (cell12765 ⟨12, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83657196523031 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (1121805380601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_13 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83622538743581 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448722960833 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨13, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83622538743581 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448722960833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_14 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (16717581088851 / 20000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448723755477 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨14, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (16717581088851 / 20000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448723755477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_15 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41776648295419 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448724560549 / 20000000000000 : ℝ))
      (E := (cell12765 ⟨15, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41776648295419 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (448724560549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_16 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (20879678037323 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (224362676931 / 10000000000000 : ℝ))
      (E := (cell12765 ⟨16, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (20879678037323 / 25000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (224362676931 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_17 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (16696830417151 / 20000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243630798571 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨17, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (16696830417151 / 20000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243630798571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_18 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (41724808183271 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243634779011 / 100000000000000 : ℝ))
      (E := (cell12765 ⟨18, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (41724808183271 / 50000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (2243634779011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12765_19 : CellCertificate 12765 (884883537582001 / 10000000000000000 : ℝ) (822733785247211 / 500000000000000000 : ℝ) (332336093560957 / 10000000000000000 : ℝ)
    (cell12765 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · norm_num [cell12765]
  · have h := gap_lower (n := 12765) (a := (83415104958141 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (224363877347 / 10000000000000 : ℝ))
      (E := (cell12765 ⟨19, by decide⟩).energy) (xi := (332336093560957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12765 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12765]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12765])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12765) (a := (83415104958141 / 100000000000000 : ℝ)) (b := (32270696687 / 20000000000000 : ℝ)) (q := (224363877347 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12765])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12765]

theorem cert12766_0 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (84074997053441 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (112172109031 / 5000000000000 : ℝ))
      (E := (cell12766 ⟨0, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (84074997053441 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (112172109031 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_1 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (42020021547539 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560861542141 / 25000000000000 : ℝ))
      (E := (cell12766 ⟨1, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (42020021547539 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560861542141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_2 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (84005114041241 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243450173893 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨2, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (84005114041241 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243450173893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_3 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83970209855493 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121727102693 / 50000000000000 : ℝ))
      (E := (cell12766 ⟨3, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83970209855493 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (1121727102693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_4 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83935330501589 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (280432276707 / 12500000000000 : ℝ))
      (E := (cell12766 ⟨4, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83935330501589 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (280432276707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_5 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (20975118985869 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243462206897 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨5, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (20975118985869 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243462206897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_6 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83865646145291 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243466193047 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨6, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83865646145291 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243466193047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_7 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83830841071357 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243470179791 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨7, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83830841071357 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243470179791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_8 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (16759212137237 / 20000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243474174559 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨8, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (16759212137237 / 20000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243474174559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_9 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83761304954473 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (224347818453 / 10000000000000 : ℝ))
      (E := (cell12766 ⟨9, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83761304954473 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (224347818453 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_10 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (837265738411 / 1000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (280435277079 / 12500000000000 : ℝ))
      (E := (cell12766 ⟨10, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (837265738411 / 1000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (280435277079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_11 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (20922966827783 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243486219467 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨11, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (20922966827783 / 25000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243486219467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_12 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (10457148166227 / 12500000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243490199393 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨12, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (10457148166227 / 12500000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243490199393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_13 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41811263931289 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560873555161 / 25000000000000 : ℝ))
      (E := (cell12766 ⟨13, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41811263931289 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560873555161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_14 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41793947437513 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (70109319719 / 3125000000000 : ℝ))
      (E := (cell12766 ⟨14, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41793947437513 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (70109319719 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_15 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41776643166473 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448700447221 / 20000000000000 : ℝ))
      (E := (cell12766 ⟨15, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41776643166473 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (448700447221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_16 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (41759351101151 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560876560327 / 25000000000000 : ℝ))
      (E := (cell12766 ⟨16, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (41759351101151 / 50000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (560876560327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_17 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83484142449233 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243510193533 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨17, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83484142449233 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243510193533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_18 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83449607040053 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243514214077 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨18, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83449607040053 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243514214077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12766_19 : CellCertificate 12766 (110606984424083 / 1250000000000000 : ℝ) (1645338633804069 / 1000000000000000000 : ℝ) (66461886516111 / 2000000000000000 : ℝ)
    (cell12766 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · norm_num [cell12766]
  · have h := gap_lower (n := 12766) (a := (83415095941253 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243518249393 / 100000000000000 : ℝ))
      (E := (cell12766 ⟨19, by decide⟩).energy) (xi := (66461886516111 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12766 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12766]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12766])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12766) (a := (83415095941253 / 100000000000000 : ℝ)) (b := (161340691653 / 100000000000000 : ℝ)) (q := (2243518249393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12766])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12766]

theorem cert12767_0 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (42037491040789 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (448664328307 / 20000000000000 : ℝ))
      (E := (cell12767 ⟨0, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (42037491040789 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (448664328307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_1 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (84040028440711 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560831414227 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨1, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (84040028440711 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560831414227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_2 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (1050063746299 / 1250000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243329632573 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨2, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (1050063746299 / 1250000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243329632573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_3 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83970195834771 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560833408781 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨3, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83970195834771 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560833408781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_4 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83935316797019 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (448667534617 / 20000000000000 : ℝ))
      (E := (cell12767 ⟨4, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83935316797019 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (448667534617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_5 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83900462554613 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (44866832777 / 2000000000000 : ℝ))
      (E := (cell12767 ⟨5, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83900462554613 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (44866832777 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_6 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83865633071689 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243345656201 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨6, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83865633071689 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243345656201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_7 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20957707078143 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (70104677341 / 3125000000000 : ℝ))
      (E := (cell12767 ⟨7, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20957707078143 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (70104677341 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_8 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (3351841929671 / 4000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (280419205551 / 12500000000000 : ℝ))
      (E := (cell12767 ⟨8, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (3351841929671 / 4000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (280419205551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_9 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (16752258564799 / 20000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243357629823 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨9, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (16752258564799 / 20000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243357629823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_10 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (41863281012057 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560840409521 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨10, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (41863281012057 / 50000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560840409521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_11 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83691855807197 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (224336567587 / 10000000000000 : ℝ))
      (E := (cell12767 ⟨11, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83691855807197 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (224336567587 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_12 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20914293534623 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560842422877 / 25000000000000 : ℝ))
      (E := (cell12767 ⟨12, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20914293534623 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (560842422877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_13 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (20905629245857 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243373691109 / 100000000000000 : ℝ))
      (E := (cell12767 ⟨13, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (20905629245857 / 25000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (2243373691109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_14 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83587884307613 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (448675536107 / 20000000000000 : ℝ))
      (E := (cell12767 ⟨14, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83587884307613 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (448675536107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_15 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83553276076833 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121690832703 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨15, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83553276076833 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121690832703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_16 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83518692257053 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121692825547 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨16, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83518692257053 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121692825547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_17 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (83484132814413 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (140211856309 / 6250000000000 : ℝ))
      (E := (cell12767 ⟨17, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (83484132814413 / 100000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (140211856309 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_18 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (8344959771523 / 10000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121696851719 / 50000000000000 : ℝ))
      (E := (cell12767 ⟨18, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (8344959771523 / 10000000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (1121696851719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12767_19 : CellCertificate 12767 (884828217361953 / 10000000000000000 : ℝ) (1645209717318753 / 1000000000000000000 : ℝ) (332282775931137 / 10000000000000000 : ℝ)
    (cell12767 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · norm_num [cell12767]
  · have h := gap_lower (n := 12767) (a := (10426885865749 / 12500000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (140212353947 / 6250000000000 : ℝ))
      (E := (cell12767 ⟨19, by decide⟩).energy) (xi := (332282775931137 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12767 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12767]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12767])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12767) (a := (10426885865749 / 12500000000000 : ℝ)) (b := (161327901911 / 100000000000000 : ℝ)) (q := (140212353947 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12767])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12767]

theorem cert12768_0 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (84074967112063 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (3589121849 / 160000000000 : ℝ))
      (E := (cell12768 ⟨0, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (84074967112063 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (3589121849 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_1 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (42020006894327 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (280400642581 / 12500000000000 : ℝ))
      (E := (cell12768 ⟨1, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (42020006894327 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (280400642581 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_2 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (84005085368871 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (280401143069 / 12500000000000 : ℝ))
      (E := (cell12768 ⟨2, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (84005085368871 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (280401143069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_3 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41985090908141 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (89728524729 / 4000000000000 : ℝ))
      (E := (cell12768 ⟨3, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41985090908141 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (89728524729 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_4 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (16787060618929 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243217128027 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨4, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (16787060618929 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243217128027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_5 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41950224583953 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (224322112429 / 10000000000000 : ℝ))
      (E := (cell12768 ⟨5, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41950224583953 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (224322112429 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_6 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (16773124000041 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560806278737 / 25000000000000 : ℝ))
      (E := (cell12768 ⟨6, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (16773124000041 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560806278737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_7 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (20957703888967 / 25000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (70100911427 / 3125000000000 : ℝ))
      (E := (cell12768 ⟨7, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (20957703888967 / 25000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (70100911427 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_8 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (83796035799407 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (224323316793 / 10000000000000 : ℝ))
      (E := (cell12768 ⟨8, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (83796035799407 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (224323316793 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_9 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41880640347761 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560809282213 / 25000000000000 : ℝ))
      (E := (cell12768 ⟨9, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41880640347761 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560809282213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_10 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41863275104547 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560810292847 / 25000000000000 : ℝ))
      (E := (cell12768 ⟨10, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41863275104547 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (560810292847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_11 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (83691844305191 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243245128059 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨11, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (83691844305191 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243245128059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_12 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (4182858147453 / 5000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (44864982427 / 2000000000000 : ℝ))
      (E := (cell12768 ⟨12, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (4182858147453 / 5000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (44864982427 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_13 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (20905626526533 / 25000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243253157437 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨13, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (20905626526533 / 25000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243253157437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_14 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (16717574748403 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (448651425193 / 20000000000000 : ℝ))
      (E := (cell12768 ⟨14, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (16717574748403 / 20000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (448651425193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_15 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (41776632911249 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (140203821801 / 6250000000000 : ℝ))
      (E := (cell12768 ⟨15, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (41776632911249 / 50000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (140203821801 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_16 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (10439835289193 / 12500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243265173243 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨16, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (10439835289193 / 12500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243265173243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_17 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (83484123181297 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121634573079 / 50000000000000 : ℝ))
      (E := (cell12768 ⟨17, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (83484123181297 / 100000000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (1121634573079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_18 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (10431198549009 / 12500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (280409148607 / 12500000000000 : ℝ))
      (E := (cell12768 ⟨18, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (10431198549009 / 12500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (280409148607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12768_19 : CellCertificate 12768 (176960112697777 / 2000000000000000 : ℝ) (411270205258431 / 250000000000000000 : ℝ) (166128061805781 / 5000000000000000 : ℝ)
    (cell12768 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · norm_num [cell12768]
  · have h := gap_lower (n := 12768) (a := (2085376947809 / 2500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243277189529 / 100000000000000 : ℝ))
      (E := (cell12768 ⟨19, by decide⟩).energy) (xi := (166128061805781 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12768 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12768]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12768])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12768) (a := (2085376947809 / 2500000000000 : ℝ)) (b := (16131511421 / 10000000000000 : ℝ)) (q := (2243277189529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12768])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12768]

theorem cert12769_0 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41052222727 / 48828125000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (140192541567 / 6250000000000 : ℝ))
      (E := (cell12769 ⟨0, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41052222727 / 48828125000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (140192541567 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_1 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (42019999569453 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121542338813 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨1, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (42019999569453 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121542338813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_2 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (84005071036093 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (35048260187 / 1562500000000 : ℝ))
      (E := (cell12769 ⟨2, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (84005071036093 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (35048260187 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_3 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41985083900013 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (70096645459 / 3125000000000 : ℝ))
      (E := (cell12769 ⟨3, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41985083900013 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (70096645459 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_4 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (2622977793577 / 3125000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560774159099 / 25000000000000 : ℝ))
      (E := (cell12769 ⟨4, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (2622977793577 / 3125000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560774159099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_5 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (20975108945839 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121550331609 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨5, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (20975108945839 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121550331609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_6 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (2096640173271 / 2500000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121552342601 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨6, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (2096640173271 / 2500000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121552342601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_7 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (20957700700311 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243108652049 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨7, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (20957700700311 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243108652049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_8 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41898011679541 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560778171781 / 25000000000000 : ℝ))
      (E := (cell12769 ⟨8, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41898011679541 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560778171781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_9 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (20940317142263 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (112155834081 / 5000000000000 : ℝ))
      (E := (cell12769 ⟨9, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (20940317142263 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (112155834081 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_10 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (2093163459901 / 2500000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243120642389 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨10, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (2093163459901 / 2500000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243120642389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_11 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (10461479100639 / 12500000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243124692187 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨11, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (10461479100639 / 12500000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243124692187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_12 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (41828575880759 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121564331607 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨12, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (41828575880759 / 50000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121564331607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_13 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (2613202975959 / 3125000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243132677753 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨13, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (2613202975959 / 3125000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243132677753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_14 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83587863178233 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560784170897 / 25000000000000 : ℝ))
      (E := (cell12769 ⟨14, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83587863178233 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560784170897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_15 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (4177662778497 / 5000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121570343169 / 50000000000000 : ℝ))
      (E := (cell12769 ⟨15, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (4177662778497 / 5000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (1121570343169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_16 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (1304979255809 / 1562500000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243144691373 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨16, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (1304979255809 / 1562500000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243144691373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_17 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83484113549883 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243148703821 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨17, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83484113549883 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243148703821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_18 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (83449579070579 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560788167583 / 25000000000000 : ℝ))
      (E := (cell12769 ⟨18, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (83449579070579 / 100000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (560788167583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12769_19 : CellCertificate 12769 (442386456886239 / 5000000000000000 : ℝ) (328990388988847 / 200000000000000000 : ℝ) (332229475620691 / 10000000000000000 : ℝ)
    (cell12769 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · norm_num [cell12769]
  · have h := gap_lower (n := 12769) (a := (20853767225089 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243156653739 / 100000000000000 : ℝ))
      (E := (cell12769 ⟨19, by decide⟩).energy) (xi := (332229475620691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12769 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12769]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12769])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12769) (a := (20853767225089 / 25000000000000 : ℝ)) (b := (161302328549 / 100000000000000 : ℝ)) (q := (2243156653739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12769])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12769]

theorem cert12770_0 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (84074937180077 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121480113847 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨0, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (84074937180077 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121480113847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_1 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (42019992245733 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242964210003 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨1, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (42019992245733 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242964210003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_2 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (16801011341117 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (448593642537 / 20000000000000 : ℝ))
      (E := (cell12770 ⟨2, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (16801011341117 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (448593642537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_3 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83970153786003 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560743046657 / 25000000000000 : ℝ))
      (E := (cell12770 ⟨3, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83970153786003 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560743046657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_4 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41967637848239 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242976198191 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨4, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41967637848239 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242976198191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_5 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83900422400961 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242980197701 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨5, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83900422400961 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242980197701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_6 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (10483199232949 / 12500000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242984193093 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨6, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (10483199232949 / 12500000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242984193093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_7 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83830790048699 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (140186762003 / 6250000000000 : ℝ))
      (E := (cell12770 ⟨7, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83830790048699 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (140186762003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_8 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83796010920797 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242992201991 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨8, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83796010920797 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242992201991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_9 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41880628222293 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242996230099 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨9, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41880628222293 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2242996230099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_10 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (10465815823119 / 12500000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243000225243 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨10, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (10465815823119 / 12500000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243000225243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_11 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41845910653481 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560751048507 / 25000000000000 : ℝ))
      (E := (cell12770 ⟨11, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41845910653481 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560751048507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_12 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41828570287933 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243008200907 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨12, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41828570287933 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243008200907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_13 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83622484357097 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121506096967 / 50000000000000 : ℝ))
      (E := (cell12770 ⟨13, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83622484357097 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (1121506096967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_14 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (16717570523253 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560754059279 / 25000000000000 : ℝ))
      (E := (cell12770 ⟨14, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (16717570523253 / 20000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560754059279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_15 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83553245319159 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243020219803 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨15, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83553245319159 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243020219803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_16 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83518662431747 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560756051371 / 25000000000000 : ℝ))
      (E := (cell12770 ⟨16, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83518662431747 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (560756051371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_17 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83484103920171 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (224302819929 / 10000000000000 : ℝ))
      (E := (cell12770 ⟨17, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83484103920171 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (224302819929 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_18 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (83449569750751 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (280379025763 / 12500000000000 : ℝ))
      (E := (cell12770 ⟨18, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (83449569750751 / 100000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (280379025763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12770_19 : CellCertificate 12770 (884745268211749 / 10000000000000000 : ℝ) (82241154452277 / 50000000000000000 : ℝ) (332202831957383 / 10000000000000000 : ℝ)
    (cell12770 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · norm_num [cell12770]
  · have h := gap_lower (n := 12770) (a := (41707529944989 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243036230571 / 100000000000000 : ℝ))
      (E := (cell12770 ⟨19, by decide⟩).energy) (xi := (332202831957383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12770 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12770]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12770])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12770) (a := (41707529944989 / 50000000000000 : ℝ)) (b := (5040298279 / 3125000000000 : ℝ)) (q := (2243036230571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12770])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12770]

theorem cert12771_0 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (21018730554401 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121419892839 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨0, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (21018730554401 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121419892839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_1 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (16807993969267 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (112142189781 / 5000000000000 : ℝ))
      (E := (cell12771 ⟨1, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (16807993969267 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (112142189781 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_2 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (84005042377347 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121423884421 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨2, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (84005042377347 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121423884421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_3 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (8397013977421 / 10000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448570354387 / 20000000000000 : ℝ))
      (E := (cell12771 ⟨3, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (8397013977421 / 10000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (448570354387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_4 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (16787052400137 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (140178484719 / 6250000000000 : ℝ))
      (E := (cell12771 ⟨4, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (16787052400137 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (140178484719 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_5 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83900409020721 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (560714946419 / 25000000000000 : ℝ))
      (E := (cell12771 ⟨5, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83900409020721 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (560714946419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_6 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83865580798461 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (140178988281 / 6250000000000 : ℝ))
      (E := (cell12771 ⟨6, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83865580798461 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (140178988281 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_7 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41915388649117 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121433892831 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨7, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41915388649117 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121433892831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_8 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41897999242277 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (280358971317 / 12500000000000 : ℝ))
      (E := (cell12771 ⟨8, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41897999242277 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (280358971317 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_9 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (20940311080531 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (224287577429 / 10000000000000 : ℝ))
      (E := (cell12771 ⟨9, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (20940311080531 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (224287577429 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_10 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83726514775829 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (280359975481 / 12500000000000 : ℝ))
      (E := (cell12771 ⟨10, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83726514775829 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (280359975481 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_11 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83691809810739 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242883807809 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨11, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83691809810739 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242883807809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_12 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (10457141174013 / 12500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121443896263 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨12, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (10457141174013 / 12500000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121443896263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_13 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (41811236742679 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121445911113 / 50000000000000 : ℝ))
      (E := (cell12771 ⟨13, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (41811236742679 / 50000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (1121445911113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_14 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83587842056111 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242895786551 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨14, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83587842056111 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242895786551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_15 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (16710647014031 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (112144990369 / 5000000000000 : ℝ))
      (E := (cell12771 ⟨15, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (16710647014031 / 20000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (112144990369 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_16 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83518652493457 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242903773771 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨16, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83518652493457 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242903773771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_17 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83484094292161 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (224290780721 / 10000000000000 : ℝ))
      (E := (cell12771 ⟨17, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83484094292161 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (224290780721 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_18 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (83449560432587 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (89716471847 / 4000000000000 : ℝ))
      (E := (cell12771 ⟨18, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (83449560432587 / 100000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (89716471847 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12771_19 : CellCertificate 12771 (221179406701429 / 2500000000000000 : ℝ) (328938850666579 / 200000000000000000 : ℝ) (664352385241 / 20000000000000 : ℝ)
    (cell12771 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · norm_num [cell12771]
  · have h := gap_lower (n := 12771) (a := (20853762720307 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242915803501 / 100000000000000 : ℝ))
      (E := (cell12771 ⟨19, by decide⟩).energy) (xi := (664352385241 / 20000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12771 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12771]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12771])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12771) (a := (20853762720307 / 25000000000000 : ℝ)) (b := (80638381673 / 50000000000000 : ℝ)) (q := (2242915803501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12771])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12771]

theorem cert12772_0 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (21018726814369 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242719396841 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨0, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (21018726814369 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242719396841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_1 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (84039955203511 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121361688319 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨1, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (84039955203511 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121361688319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_2 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (84005028051379 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121363689151 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨2, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (84005028051379 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121363689151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_3 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83970125764649 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140170713163 / 6250000000000 : ℝ))
      (E := (cell12772 ⟨3, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83970125764649 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (140170713163 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_4 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (20983812076771 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242735366247 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨4, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (20983812076771 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242735366247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_5 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (20975098910659 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (280342421151 / 12500000000000 : ℝ))
      (E := (cell12772 ⟨5, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (20975098910659 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (280342421151 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_6 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83865567735447 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242743369537 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨6, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83865567735447 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242743369537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_7 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (41915382274923 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242747374913 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨7, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (41915382274923 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242747374913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_8 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83795986050351 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (56068784819 / 2500000000000 : ℝ))
      (E := (cell12772 ⟨8, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83795986050351 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (56068784819 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_9 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83761232201663 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (35043052691 / 1562500000000 : ℝ))
      (E := (cell12772 ⟨9, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83761232201663 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (35043052691 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_10 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83726502968671 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121379689103 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨10, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83726502968671 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121379689103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_11 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (41845899158221 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242763417381 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨11, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (41845899158221 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242763417381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_12 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83657118210231 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (89710695199 / 4000000000000 : ℝ))
      (E := (cell12772 ⟨12, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83657118210231 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (89710695199 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_13 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (8362246261547 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (448554277653 / 20000000000000 : ℝ))
      (E := (cell12772 ⟨13, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (8362246261547 / 10000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (448554277653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_14 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83587831497771 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121387695019 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨14, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83587831497771 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121387695019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_15 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (83553224822927 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (280347423863 / 12500000000000 : ℝ))
      (E := (cell12772 ⟨15, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (83553224822927 / 100000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (280347423863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_16 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (16703728511381 / 20000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121391698117 / 50000000000000 : ℝ))
      (E := (cell12772 ⟨16, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (16703728511381 / 20000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (1121391698117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_17 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (20871021166463 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242787411153 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨17, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (20871021166463 / 25000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242787411153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_18 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (41724775558043 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242791440547 / 100000000000000 : ℝ))
      (E := (cell12772 ⟨18, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (41724775558043 / 50000000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (2242791440547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12772_19 : CellCertificate 12772 (884689989553397 / 10000000000000000 : ℝ) (328913087560311 / 200000000000000000 : ℝ) (332149557608903 / 10000000000000000 : ℝ)
    (cell12772 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · norm_num [cell12772]
  · have h := gap_lower (n := 12772) (a := (10426880234263 / 12500000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (280349428849 / 12500000000000 : ℝ))
      (E := (cell12772 ⟨19, by decide⟩).energy) (xi := (332149557608903 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12772 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12772]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12772])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12772) (a := (10426880234263 / 12500000000000 : ℝ)) (b := (161263983803 / 100000000000000 : ℝ)) (q := (280349428849 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12772])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12772]

theorem cert12773_0 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16814978459939 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (448519800673 / 20000000000000 : ℝ))
      (E := (cell12773 ⟨0, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16814978459939 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (448519800673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_1 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16807988112599 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242603010899 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨1, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16807988112599 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242603010899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_2 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (84005013727679 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242607041069 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨2, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (84005013727679 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242607041069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_3 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41985055878659 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121305522381 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨3, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41985055878659 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121305522381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_4 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (20983808653919 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (112130751521 / 5000000000000 : ℝ))
      (E := (cell12773 ⟨4, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (20983808653919 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (112130751521 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_5 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16780076453341 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121309503117 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨5, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16780076453341 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121309503117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_6 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83865554674549 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (560655759523 / 25000000000000 : ℝ))
      (E := (cell12773 ⟨6, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83865554674549 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (560655759523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_7 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83830751803537 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121313508891 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨7, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83830751803537 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121313508891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_8 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (20948993404547 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (112131550533 / 5000000000000 : ℝ))
      (E := (cell12773 ⟨8, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (20948993404547 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (112131550533 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_9 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16752244016641 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242635023899 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨9, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16752244016641 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242635023899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_10 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83726491163477 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (112131953221 / 5000000000000 : ℝ))
      (E := (cell12773 ⟨10, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83726491163477 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (112131953221 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_11 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83691786824073 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (448528604549 / 20000000000000 : ℝ))
      (E := (cell12773 ⟨11, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83691786824073 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (448528604549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_12 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83657107030247 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242647021353 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨12, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83657107030247 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242647021353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_13 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83622451747433 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242651066417 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨13, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83622451747433 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242651066417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_14 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16717564188249 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242655047577 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨14, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16717564188249 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242655047577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_15 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (41776607288737 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242659028543 / 100000000000000 : ℝ))
      (E := (cell12773 ⟨15, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (41776607288737 / 50000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (2242659028543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_16 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (20879658155523 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121331536437 / 50000000000000 : ℝ))
      (E := (cell12773 ⟨16, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (20879658155523 / 25000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (1121331536437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_17 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83484075041243 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280333383667 / 12500000000000 : ℝ))
      (E := (cell12773 ⟨17, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83484075041243 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280333383667 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_18 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (83449541801249 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (112133554049 / 5000000000000 : ℝ))
      (E := (cell12773 ⟨18, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (83449541801249 / 100000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (112133554049 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12773_19 : CellCertificate 12773 (884662356453811 / 10000000000000000 : ℝ) (1644436642446781 / 1000000000000000000 : ℝ) (332122926921453 / 10000000000000000 : ℝ)
    (cell12773 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · norm_num [cell12773]
  · have h := gap_lower (n := 12773) (a := (16683006573721 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280334381773 / 12500000000000 : ℝ))
      (E := (cell12773 ⟨19, by decide⟩).energy) (xi := (332122926921453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12773 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12773]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12773])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12773) (a := (16683006573721 / 20000000000000 : ℝ)) (b := (80625603149 / 50000000000000 : ℝ)) (q := (280334381773 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12773])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12773]

theorem cert12774_0 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (42037438672129 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242478720891 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨0, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (42037438672129 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242478720891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_1 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16807985184957 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448496539681 / 20000000000000 : ℝ))
      (E := (cell12774 ⟨1, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16807985184957 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448496539681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_2 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (84004999406247 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242486699279 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨2, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (84004999406247 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242486699279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_3 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41985048876109 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448498146457 / 20000000000000 : ℝ))
      (E := (cell12774 ⟨3, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41985048876109 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448498146457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_4 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (4196761046323 / 5000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448498938023 / 20000000000000 : ℝ))
      (E := (cell12774 ⟨4, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (4196761046323 / 5000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448498938023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_5 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (81933953997 / 97656250000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448499739351 / 20000000000000 : ℝ))
      (E := (cell12774 ⟨5, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (81933953997 / 97656250000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (448499739351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_6 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41932770807883 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (280312837781 / 12500000000000 : ℝ))
      (E := (cell12774 ⟨6, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41932770807883 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (280312837781 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_7 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16766147811861 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242506714271 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨7, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16766147811861 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242506714271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_8 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16759192237613 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121255341121 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨8, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16759192237613 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121255341121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_9 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83761207966749 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242514729319 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨9, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83761207966749 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242514729319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_10 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41863239680123 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242518688339 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨10, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41863239680123 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242518688339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_11 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83691775333629 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121261370027 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨11, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83691775333629 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121261370027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_12 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (1673141917043 / 2000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242526716663 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨12, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (1673141917043 / 2000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242526716663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_13 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (41811220440623 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121265370221 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨13, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (41811220440623 / 50000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121265370221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_14 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83587810386531 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242534701027 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨14, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83587810386531 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242534701027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_15 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83553204333797 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242538720299 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨15, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83553204333797 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242538720299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_16 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (10439827836127 / 12500000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121271372751 / 50000000000000 : ℝ))
      (E := (cell12774 ⟨16, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (10439827836127 / 12500000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (1121271372751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_17 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (16696813083667 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (280318340443 / 12500000000000 : ℝ))
      (E := (cell12774 ⟨17, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (16696813083667 / 20000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (280318340443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_18 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (3337981299523 / 4000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560637679369 / 25000000000000 : ℝ))
      (E := (cell12774 ⟨18, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (3337981299523 / 4000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (560637679369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

theorem cert12774_19 : CellCertificate 12774 (442317363752989 / 5000000000000000 : ℝ) (1644307867263831 / 1000000000000000000 : ℝ) (332096300557013 / 10000000000000000 : ℝ)
    (cell12774 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · norm_num [cell12774]
  · have h := gap_lower (n := 12774) (a := (83415023864733 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242554731939 / 100000000000000 : ℝ))
      (E := (cell12774 ⟨19, by decide⟩).energy) (xi := (332096300557013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12774 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12774]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12774])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12774) (a := (83415023864733 / 100000000000000 : ℝ)) (b := (16123843083 / 10000000000000 : ℝ)) (q := (2242554731939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12774])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12774]

end BstLean.Part268
